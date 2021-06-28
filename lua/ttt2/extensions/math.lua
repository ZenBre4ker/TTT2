---
-- A bunch of random function bundled in the math module
-- It massively improves the randomness of the math library
-- @author ZenBre4ker
-- @module math

if SERVER then
	AddCSLuaFile()
end

local exp = math.exp
local floor = math.floor

---
-- Equivalent to ExponentialDecay from Source's mathlib.
-- Convenient for falloff curves.
-- @param number halflife
-- @param number dt
-- @return number
-- @realm shared
function math.ExponentialDecay(halflife, dt)
	-- ln(0.5) = -0.69..
	return exp((-0.69314718 / halflife) * dt)
end

--[[
	The following Mersenne Twister Lua Implementation is mostly taken from:

	Source: https://github.com/davebollinger/mt19937ar-lua
	mt19937ar.lua, a conversion of the Jan 26 2002 version of mt19937ar.c
	ref:  http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/MT2002/emt19937ar.html
	Copyright (C) 2016 David Bollinger (davebollinger at gmail dot com)

	Which itself derives of the C Implementation of:

	A C-program for MT19937, with initialization improved 2002/1/26.
	Coded by Takuji Nishimura and Makoto Matsumoto.
	Before using, initialize the state by using init_genrand(seed)  
	or init_by_array(init_key, key_length).
	Copyright (C) 1997 - 2002, Makoto Matsumoto and Takuji Nishimura,
	All rights reserved.                          
	Redistribution and use in source and binary forms, with or without
	modification, are permitted provided that the following conditions
	are met:
		1. Redistributions of source code must retain the above copyright
			notice, this list of conditions and the following disclaimer.
		2. Redistributions in binary form must reproduce the above copyright
			notice, this list of conditions and the following disclaimer in the
			documentation and/or other materials provided with the distribution.
		3. The names of its contributors may not be used to endorse or promote 
			products derived from this software without specific prior written 
			permission.
	THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
	"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
	LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
	A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT OWNER OR
	CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
	EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
	PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
	PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
	LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
	NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
	SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
	Any feedback is very welcome.
	http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/emt.html
	email: m-mat @ math.sci.hiroshima-u.ac.jp (remove space)
--]]

---
-- a 32bitUL * 32bitUL = 64bitUL can overflow the 53-bit precision of a double
-- (thus potentially corrupting the lower 32-bits)
-- this "longhand method" 48-bit version ignores the (unneeded) hiword * hiword
-- portion to avoid overflow of intermediate result prior to truncation to 32-bits
-- (only used when seeding, not when generating, so performance considerations should be negligible)
-- @param a number a "32-bit integer"
-- @param b number a "32-bit integer"
-- @return number the "32-bit integer" result of multiplication
local function SAFEMUL32(a,b)
	local alo = floor(a % 65536)
	local ahi = floor(a / 65536) % 65536
	local blo = floor(b % 65536)
	local bhi = floor(b / 65536) % 65536
	local lolo = alo * blo
	local lohi = alo * bhi
	local hilo = ahi * blo
	local llhh = lohi + hilo
	return floor((llhh * 65536 + lolo) % 4294967296)
end

---
-- 32-bit bitwise and
-- @param a number a "32-bit integer"
-- @param b number a "32-bit integer"
-- @return number the "32-bit integer" result of the bitwise operation
local function AND(a, b)
	local r, p = 0, 1

	for i = 0, 31 do
		local a1 = a % 2
		local b1 = b % 2
		if a1 > 0 and b1 > 0 then
			r = r + p
		end

		if a1 > 0 then
			a = a - 1
		end

		if b1 > 0 then
			b = b - 1
		end

		a = a / 2
		b = b / 2
		p = p * 2
	end

	return r
end

---
-- 32-bit bitwise or
-- @param a number a "32-bit integer"
-- @param b number a "32-bit integer"
-- @return number the "32-bit integer" result of the bitwise operation
local function OR(a, b)
	local r, p = 0, 1

	for i = 0, 31 do
		local a1 = a % 2
		local b1 = b % 2

		if a1 > 0 or b1 > 0 then
			r = r + p
		end

		if a1 > 0 then
			a = a - 1
		end

		if b1 > 0 then
			b = b - 1
		end

		a = a / 2
		b = b / 2
		p = p * 2
	end

	return r
end

---
-- 32-bit bitwise xor
-- @param a number a "32-bit integer"
-- @param b number a "32-bit integer"
-- @return number the "32-bit integer" result of the bitwise operation
local function XOR(a, b)
	local r,p = 0,1

	for i = 0, 31 do
		local a1 = a % 2
		local b1 = b % 2

		if (a1 ~= b1) then
			r = r + p
		end

		if (a1 > 0) then
			a = a - 1
		end

		if (b1 > 0) then
			b = b - 1
		end

		a = a / 2
		b = b / 2
		p = p * 2
	end

	return r
end

--- various bitwise shifts and masks
local SHR1 = function(y) return floor(y / 2) end
local SHR30 = function(y) return floor(y / 1073741824) end
local SHR11 = function(y)  return floor(y / 2048)  end
local SHL7 = function(y)  return y * 128  end
local SHL15 = function(y)  return y * 32768  end
local SHR18 = function(y)  return floor(y / 262144)  end
local BIT0 = function(y) return y % 2 end -- should not be necessary to floor() this result, given its usage exclusively on "ints"

--------------------------------
-- END INTERNAL SUPPORT STUFF
-- BEGIN ACTUAL MERSENNE TWISTER
--------------------------------

local N = 624
local M = 397

local MATRIX_A = 0x9908B0DF
local UPPER_MASK = 0x80000000
local LOWER_MASK = 0x7FFFFFFF

local mt = {}
local mti = N + 1

---
-- @description seed the generator via number
-- @param s number representing a 32-bit integer seed value
function math.randomseed(s)
	mt[0] = AND(s, 0xFFFFFFFF)

	for i = 1, N-1 do
		-- mt[i] = 1812433253 * XOR(mt[i-1], SHR30(mt[i-1])) + i -- the literal translation, but nope
		mt[i] = SAFEMUL32(1812433253, XOR(mt[i-1], SHR30(mt[i-1]))) + i -- yep
		mt[i] = AND(mt[i], 0xFFFFFFFF)
	end

	mti = N
end

--- generates a random number on [0,0xffffffff]-interval
function math.genrand_int32()
	local y

	if mti >= N then
		if mti == N + 1 then
			math.randomseed(5489)
		end

		for kk = 0, N-M-1 do
			y = OR( AND(mt[kk],UPPER_MASK) , AND(mt[kk + 1],LOWER_MASK) )
			mt[kk] = XOR(mt[kk + M], XOR( SHR1(y), BIT0(y) * MATRIX_A ))
			kk = kk + 1
		end

		for kk = N-M, N-2 do
			y = OR( AND(mt[kk],UPPER_MASK) , AND(mt[kk + 1],LOWER_MASK) )
			mt[kk] = XOR(mt[kk + (M - N)], XOR( SHR1(y), BIT0(y) * MATRIX_A ))
			kk = kk + 1
		end

		y = OR( AND(mt[N-1],UPPER_MASK) , AND(mt[0],LOWER_MASK) )
		mt[N-1] = XOR(mt[M-1], XOR( SHR1(y), BIT0(y) * MATRIX_A ))
		mti = 0
	end

	y = mt[mti]
	mti = mti + 1
	y = XOR(y, SHR11(y))
	y = XOR(y, AND(SHL7(y), 0x9D2C5680) )
	y = XOR(y, AND(SHL15(y), 0xEFC60000) )
	y = XOR(y, SHR18(y))

	return y
end

-- Floating Point Versions

--- generates a random number on [0,1]-real-interval
function math.genrand_real1()
	return math.genrand_int32() * (1.0 / 4294967295.0) -- divided by 2^32-1
end

--- generates a random number on [0,1)-real-interval
function math.genrand_real2()
	return math.genrand_int32() * (1.0 / 4294967296.0) -- divided by 2^32
end

--- a math library work-alike for generating random numbers
function math.random(m,n)
	if (not m) then
		-- handle zero-argument form
		return math.genrand_real2()
	else
		if (not n) then
			-- handle one-argument form
			return math.genrand_int32() % m + 1
		else
			-- handle two-argument form
			return m + math.genrand_int32() % (n - m + 1)
		end
	end
end

function math.Rand(min, max)
	return min + math.genrand_real1() *  (max - min)
end
