local Static = {}
local BigInt = { __type = 'BigInt' }
local BigIntMT = { __index = BigInt }

local BASE = 2^32
local KARATSUBA_TRESHOLD = 2 -- in chunks

local BASE_BIGINT: BigInt

type Chunks = {number}
type BigIntOptional = BigInt | number | string

local function computeDecimalBlockSize(b)
    local factor = 1
    local digits = 0
    while factor * 10 < b do
        factor *= 10
        digits += 1
    end
    return factor, digits
end

local blockFactor, digitsCount = computeDecimalBlockSize(BASE)

--[[
    Converts `a` to BigInt when appropriate
    @internal
]]
local function fixToBigInt(a: BigIntOptional): BigInt
	if type(a) == 'number' then
		return Static.fromInt(a)
	elseif type(a) == 'string' then
		return Static.fromString(a)
	elseif a.__type == 'BigInt' then
		return a
	else
		error('[Gigantix | BigInt] Must be a number or a BigInt')
	end
end

--[[
    Propagate carries to make sure each chunk doesn't exceed BASE-1
    @internal
]]
local function mutPrune(chunks: Chunks)
	while #chunks > 1 and chunks[#chunks] == 0 do
        table.remove(chunks)
	end

	return chunks
end

--[[
    Propagate carries to make sure each chunk doesn't exceed `BASE-1`, and prunes any trailing zeroes
    @internal
]]
local function mutNormalizeAndPrune(chunks: Chunks)
	local carry = 0
	local lastNonZero = 0

	local cI = 1 -- carry index
	local n = #chunks

	while cI <= n or carry > 0 do
		local current = (chunks[cI] or 0) + carry
		local newVal = current % BASE
		carry = current // BASE

		if cI <= n or newVal ~= 0 then
			chunks[cI] = newVal
		end

		if newVal ~= 0 then
			lastNonZero = cI
		end

		cI += 1
		if cI > n and carry > 0 then
			n += 1
		end
	end
		
	if lastNonZero == 0 then
		chunks[1] = 0
		for i = 2, #chunks do
			chunks[i] = nil
		end
	else
		for i = #chunks, lastNonZero + 1, -1 do
			chunks[i] = nil
		end
	end

	return chunks
end

local function nextPowerOf2(n)
	local p = 1
	while p < n do
		p *= 2
	end
	return p
end

local function pad(chunks)
	local L = nextPowerOf2(#chunks)
	local padded = {}
	for i = 1, L do
		padded[i] = chunks[i] or 0
	end
	return padded
end

--[[
   Constructs a new BigInt object from chunks and sign
]]
function Static.new(chunks: Chunks, sign: number?)
	local self = setmetatable({
		chunks = mutNormalizeAndPrune(table.clone(chunks)),
		sign = sign or 1,
	}, BigIntMT)

	return self
end

--[[
   Constructs a new BigInt object from a native int
]]
function Static.fromInt(n: number): BigInt -- n is a native number, not a big int
    if n == 0 then return Static.zero() end

	assert(math.floor(n) == n, `[Gigantix | BigInt] n must be a whole number: {n}`)

	local sign = if n < 0 then -1 else 1
	n = math.abs(n)

	local chunks = {}

	if n ~= 0 then
		while n > 0 do
			table.insert(chunks, n % BASE)
			n //= BASE
		end
	end

	return Static.new(chunks, sign)
end

function Static.fromString(str: string): BigInt
	if str:match('%D+') then -- anything else in the str
		return Static.fromScientific(str)
	else
		return Static.fromDecimal(str)
	end
end

function Static.fromDecimal(str: string): BigInt
	local signStr, decimalStr = str:match('^([%+%-]?)([0-9]+)')
	signStr = signStr or '+'

	assert(decimalStr, `[Gigantix | BigInt] Invalid decimal string: {str}`)

	local result = Static.zero()

	for i = 1, #decimalStr do
		local digit = tonumber(decimalStr:sub(i, i))
		assert(digit ~= nil, `[Gigantix | BigInt] Invalid digit at position {i}: {str:sub(i, i)}`)

		result = result * Static.ten() + Static.fromInt(digit)
	end

	local sign = if signStr == '-' then -1 else 1
	result.sign = sign

	return result
end

function Static.fromScientific(str: string): BigInt
	--[[
		^[%+%-]? = at the start, get the sign (if no sign is found, then assume its positive)
		%d*%.?%d+ = get the fractional (or integer) mantissa, integer part could be ommited such as .1, .05, etc...
		[eE] = matches e or E (as in 1e10 or 1E10)
	]]
    local signStr, mantissaIntStr, mantissaFracStr, expStr = str:match("^([%+%-]?)(%d*)%.?(%d+)[eE]([%+%-]?%d+)$")

    assert(mantissaIntStr, `[Gigantix | BigInt] Invalid mantissa in scientific notation: {str}`)
	assert(mantissaFracStr, `[Gigantix | BigInt] Invalid mantissa in scientific notation: {str}`)
    assert(expStr, `[Gigantix | BigInt] Invalid exponent in scientific notation: {str}`)

	local sign = if signStr == '-' then -1 else 1

	local exponent = Static.fromDecimal(expStr)

	local fracCount = #mantissaFracStr
	local combined = `{mantissaIntStr}{mantissaFracStr}`

	local result = Static.fromDecimal(combined)
    result.sign = sign

    local effectiveShift = exponent - fracCount
    assert(effectiveShift >= Static.zero(), "[Gigantix | BigInt] Fractional values (negative effective exponent) not supported.")

	-- blame roblox type solver for this
    local multiplier = Static.ten() ^ effectiveShift
    
    local finalResult = result * multiplier
    return finalResult
end

--[[
   Constructs a new zero BigInt object
]]
function Static.zero()
    return Static.new({0})
end

--[[
   Constructs a new one BigInt object
]]
function Static.one()
	return Static.fromInt(1)
end

--[[
   Constructs a new ten BigInt object
]]
function Static.ten()
	return Static.fromInt(10)
end


--[[
	Creates a clone of the BigInt
	@internal
]]
function BigInt.clone(self: BigInt): BigInt
	return Static.new(table.clone(self.chunks), self.sign)
end

--[[
   Gets the multiplication product of 2 BigInts using the grade-school algorithm (or long multiplication)
]]
function BigInt.gradeMultiply(self: BigInt, b: BigInt)
	local lenProduct = #self.chunks + #b.chunks
	local result = table.create(lenProduct, 0)

	for i = 1, #self.chunks do
		local carry = 0

		for j = 1, #b.chunks do
			local k = i + j - 1 -- little endian
			local prod = self.chunks[i] * b.chunks[j] + result[k] + carry

			result[k] = prod % BASE
			carry = prod // BASE
		end
        
		result[i + #b.chunks] += carry
	end

	return Static.new(result, self.sign * b.sign)
end

function BigInt.iterativeKaratsuba(self: BigInt, b: BigInt)
	local A = pad(self.chunks)
	local B = pad(b.chunks)
	local L = #A -- a power of 2

	-- wrap each chunk as a BigInt
	local segments = {}
	for i = 1, L do
		segments[i] = {
			Static.new({ A[i] }, 1),
			Static.new({ B[i] }, 1),
		}
	end

	-- cache shift factors: shifts[i] = BASE^i
	local shiftCache = {
		[0] = Static.one(),
	}

	local function getShift(n: number): BigInt
		if shiftCache[n] then
			return shiftCache[n]
		end

		-- Build from the largest known previous shift
		local maxKnown = n - 1
		while not shiftCache[maxKnown] and maxKnown > 0 do
			maxKnown -= 1
		end

		local result = shiftCache[maxKnown]
		for i = maxKnown + 1, n do
			result = result:gradeMultiply(BASE_BIGINT)
			shiftCache[i] = result
		end

		return result
	end

	local segmentSize = 1

	while #segments > 1 do
		local newSegments = {}

		for i = 1, #segments, 2 do
			local sa = segments[i]
			local sb = segments[i + 1]

			local A0, A1 = sa[1], sb[1]
			local B0, B1 = sa[2], sb[2]

			local z0 = A0 * B0
			local z2 = A1 * B1

			local mid = (A0 + A1) * (B0 + B1)

			local shift1 = getShift(segmentSize)
			local shift2 = getShift(segmentSize * 2)

			local combined = z2 * shift2 + (mid - z0 - z2) * shift1 + z0

			table.insert(newSegments, {combined, Static.one()})
		end

		segments = newSegments
		segmentSize *= 2
	end

	local prod = segments[1][1]
	prod.sign = self.sign * b.sign

	return prod
end

@native
function BigInt.divMod(self: BigInt, b: BigIntOptional): (BigInt, BigInt)
	local divisor = fixToBigInt(b)

	if #divisor.chunks == 1 and divisor.chunks[1] == 0 then
		return Static.zero(), Static.zero()
	end

	local signQuot = self.sign * divisor.sign
	local absDividend = Static.new(table.clone(self.chunks), 1)
	local absDivisor = Static.new(table.clone(divisor.chunks), 1)

	local n = #absDivisor.chunks
	local m = #absDividend.chunks - n

	if m < 0 then
		-- Dividend is smaller than divisor
		return Static.zero(), self:clone()
	end

	-- Normalize so that most significant digit of divisor >= BASE // 2
	local d = math.floor(BASE / (absDivisor.chunks[n] + 1))

	local function mulByInt(chunks: Chunks, k: number)
		local result = {}
		local carry = 0
		for i = 1, #chunks do
			local prod = chunks[i] * k + carry
			result[i] = prod % BASE
			carry = prod // BASE
		end
		if carry > 0 then
			table.insert(result, carry)
		end
		return result
	end

	local U = mulByInt(absDividend.chunks, d)
	local V = mulByInt(absDivisor.chunks, d)

	-- Ensure U has an extra slot for overflow
	if #U == m + n then
		U[m + n + 1] = 0
	end

	local Q = table.create(m + 1, 0)

	for j = m, 0, -1 do
		local uj_n1 = U[j + n + 1] or 0
		local uj_n0 = U[j + n] or 0
		local numerator = uj_n1 * BASE + uj_n0
		local v_n1 = V[n] or 1

		local qhat = math.floor(numerator / v_n1)
		if qhat >= BASE then qhat = BASE - 1 end

		-- Multiply and subtract
		local borrow = 0
		for i = 1, n do
			local p = qhat * (V[i] or 0)
			local uIdx = j + i
			local diff = (U[uIdx] or 0) - p % BASE - borrow
			borrow = p // BASE

			if diff < 0 then
				diff = diff + BASE
				borrow = borrow + 1
			end
			U[uIdx] = diff
		end

		-- Adjust for final borrow
		local finalIdx = j + n + 1
		U[finalIdx] = (U[finalIdx] or 0) - borrow

		if U[finalIdx] < 0 then
			-- Too big: decrement qhat and add V back
			qhat = qhat - 1
			local carry = 0
			for i = 1, n do
				local uIdx = j + i
				local sum = (U[uIdx] or 0) + (V[i] or 0) + carry
				U[uIdx] = sum % BASE
				carry = sum // BASE
			end
			U[finalIdx] = (U[finalIdx] or 0) + carry
		end

		Q[j + 1] = qhat
	end

	-- De-normalize remainder
	local function divByInt(chunks, k)
		local result = {}
		local carry = 0
		for i = #chunks, 1, -1 do
			local num = carry * BASE + chunks[i]
			local q = math.floor(num / k)
			carry = num % k
			result[i] = q
		end
		mutNormalizeAndPrune(result)
		return result
	end

	local R = if d > 1 then divByInt(U, d) else U

	mutPrune(Q)
	mutPrune(R)

	local quotient = Static.new(Q, signQuot)
	local remainder = Static.new(R, self.sign)

	return quotient, remainder
end

--[[
	Compares the absolute value of 2 BigInts
	@internal
]]
function BigInt.compareAbs(self: BigInt, other: BigInt): number
	if #self.chunks ~= #other.chunks then
		return if #self.chunks > #other.chunks then 1 else -1
	end

	for i = #self.chunks, 1, -1 do
		if self.chunks[i] ~= other.chunks[i] then
			return if self.chunks[i] > other.chunks[i] then 1 else -1
		end
	end

	return 0
end

--[[
	Compares the absolute value of 2 BigInts. Returns `1` if greather than, `-1` if lesser than, `0` if equal to
	@internal
]]
function BigInt.compare(self: BigInt, other: BigInt): number
    if self.sign ~= other.sign then
        return self.sign < other.sign and -1 or 1
    end

	local sign = self.sign

	if #self.chunks ~= #other.chunks then
		-- if self abs value is bigger than other and both sign are negative
		return if #self.chunks > #other.chunks and sign < 0 then 1 else -1
	end

	for i = #self.chunks, 1, -1 do
		if self.chunks[i] ~= other.chunks[i] then
			-- if self abs value is bigger than other and both sign are negative
			return if self.chunks[i] > other.chunks[i] and sign < 0 then 1 else -1
		end
	end

	return 0
end

function BigIntMT.__eq(a: BigInt, b: BigInt)
    return a:compare(b) == 0
end

function BigIntMT.__lt(a: BigInt, b: BigInt)
    return a:compare(b) < 0
end

function BigIntMT.__le(a: BigInt, b: BigInt)
    return a:compare(b) <= 0
end

function BigIntMT.__add(_a: BigIntOptional, _b: BigIntOptional): BigInt
    local a = fixToBigInt(_a)
    local b = fixToBigInt(_b)

	if a.sign == b.sign then
		local result = {}
		local carry = 0
		local maxLen = math.max(#a.chunks, #b.chunks)
		for i = 1, maxLen do
			local aD = a.chunks[i] or 0
			local bD = b.chunks[i] or 0
			local sum = aD + bD + carry

			result[i] = sum % BASE
			carry = sum // BASE
		end

		while carry > 0 do
			table.insert(result, carry % BASE)
			carry //= BASE
		end

		return Static.new(result, a.sign)
	else
		-- a + b = a - (-b)
		local nOther = Static.new(b.chunks, -b.sign)
		return a - nOther
	end
end

--[[
   Gets the difference of a to b
]]
function BigIntMT.__sub(_a: BigIntOptional, _b: BigIntOptional): BigInt
	local a = fixToBigInt(_a)
	local b = fixToBigInt(_b)

	if a.sign ~= b.sign then
		-- a - b = a + (-b)
		local nOther = Static.new(b.chunks, -b.sign)
		return a + nOther
	else
		-- subtract the smaller absolute value from the larger absolute value.
		local cmp = a:compareAbs(b)
		if cmp == 0 then
			return Static.zero()
		end

		local result = {}
		local borrow = 0

		local l, s, sign

		if cmp > 0 then
			l = a
			s = b
			sign = a.sign
		else
			l = b
			s = a
			sign = -a.sign
		end

		local maxLen = math.max(#l.chunks, #s.chunks)

		for i = 1, maxLen do
			local dL = l.chunks[i] or 0
			local dS = s.chunks[i] or 0
			local diff = dL - dS - borrow

			if diff < 0 then
				diff += BASE
				borrow = 1
			else
				borrow = 0
			end

			result[i] = diff
		end

		return Static.new(result, sign)
	end
end

function BigIntMT.__mul(_a: BigIntOptional, _b: BigIntOptional): BigInt
	if _a == 0 or _b == 0 then
		return Static.zero()
	end

	local a = fixToBigInt(_a)
	local b = fixToBigInt(_b)

    local maxLen = math.max(#a.chunks, #b.chunks)

    if maxLen >= KARATSUBA_TRESHOLD then
        return a:iterativeKaratsuba(b) 
    else
        return a:gradeMultiply(b)
    end
end

function BigIntMT.__div(_a: BigIntOptional, _b: BigIntOptional): BigInt
    local a = fixToBigInt(_a)
	local b = fixToBigInt(_b)
    local q = a:divMod(b)
    return q
end
BigIntMT.__idiv = BigIntMT.__div

function BigIntMT.__mod(_a: BigIntOptional, _b: BigIntOptional): BigInt
    local a = fixToBigInt(_a)
	local b = fixToBigInt(_b)
    local _, r = a:divMod(b)
    return r
end

function BigIntMT.__unm(self: BigInt): BigInt
	local result = self:clone()
	result.sign *= -1

	return result
end

function BigIntMT.__pow(_a: BigIntOptional, _b: BigIntOptional): BigInt
	local a = fixToBigInt(_a)
	local exp = fixToBigInt(_b)

	local result = Static.one()
    local base = a:clone()

	local zero, one = Static.zero(), Static.one()
    
    while exp > zero do
        if exp % 2 == one then
            result *= base  -- use the BigInt multiplication
        end
		base *= base
        exp //= 2
    end

    return result
end

BASE_BIGINT = Static.fromInt(BASE)

type BigInt = typeof(Static.new(...))

return Static
