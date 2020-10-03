---
-- @section Scoring
-- @desc Server and client both need this for scoring event logs

local pairs = pairs
local IsValid = IsValid

---
-- Initializes the score table
-- @return table
-- @realm shared
function ScoreInit()
	local _tbl = {
		deaths = 0,
		suicides = 0,
		lt = "", -- last team
		lr = "", -- last role
		ev = { -- on doing a kill event with different data
			--r = ROLE_NONE, -- subrole at the moment of the event
			--t = "", -- team at the moment of the event
			--v = "" -- victims team at the moment of the event
		},
		bonus = 0 -- non-kill points to add
	}

	return _tbl
end

---
-- Initializes a score evenet
-- @return table
-- @realm shared
function ScoreEventInit()
	local _tbl = {
		r = ROLE_NONE, -- subrole at the moment of the event
		t = "", -- team at the moment of the event
		v = "" -- victims team at the moment of the event
	}

	return _tbl
end

---
-- Inserts a score event into the scores table
-- @param table score event
-- @param table scores scores table
-- @realm shared
function ScoreEvent(e, scores)
	if e.id == EVENT_KILL then
		local aid = e.att.sid64
		local vid = e.vic.sid64

		-- make sure a score table exists for this person
		-- he might have disconnected by now
		scores[vid] = scores[vid] or ScoreInit()

		-- normally we have the ply:GetTraitor stuff to base this on, but that
		-- won't do for disconnected players
		scores[aid] = scores[aid] or ScoreInit()

		scores[vid].deaths = scores[vid].deaths + 1
		scores[vid].lt = e.vic.t
		scores[vid].lr = e.vic.r

		if aid == vid then
			scores[vid].suicides = scores[vid].suicides + 1
		elseif aid ~= -1 then
			local eva = ScoreEventInit()
			eva.r = e.att.r
			eva.t = e.att.t
			eva.v = e.vic.t

			scores[aid].ev[#scores[aid].ev + 1] = eva
			scores[aid].lt = e.att.t
			scores[aid].lr = e.att.r
		end
	elseif e.id == EVENT_BODYFOUND then
		local sid64 = e.sid64

		scores[sid64] = scores[sid64] or ScoreInit()

		if e.t == TEAM_TRAITOR then return end

		local find_bonus = e.r == ROLE_DETECTIVE and 3 or 1

		scores[sid64].bonus = scores[sid64].bonus + find_bonus
	end
end

---
-- Events should be event log as generated by scoring.lua
-- scores should be table with SteamIDs as keys
-- The method of finding these IDs differs between server and client
-- @param table events scores events table
-- @param table scores scores table
-- @return table scores list
-- @realm shared
function ScoreEventLog(events, scores)
	for k in pairs(scores) do
		scores[k] = ScoreInit()
	end

	for _, e in pairs(events) do
		ScoreEvent(e, scores)
	end

	return scores
end

---
-- Returns the score bonus the winner team has
-- @param table scores scores table
-- @param string wintype a @{ROLE}'s team, the winner team
-- @return number bonus points
-- @realm shared
function ScoreTeamBonus(scores, wintype)
	local alive = {}
	local dead = {}

	-- who's alive, who dead?
	for _, sc in pairs(scores) do
		local state = (sc.deaths == 0) and alive or dead

		local team = sc.lt
		if team ~= TEAM_NONE then
			state[team] = (state[team] or 0) + 1
		end
	end

	local bonus = {}

	for id, sc in pairs(scores) do
		local team = sc.lt
		local roleData = roles.GetByIndex(sc.lr)
		local others = 0

		for other, amount in pairs(dead) do
			if team == TEAM_NONE or team ~= other or TEAMS[team].alone then
				others = others + amount
			end
		end

		bonus[id] = (alive[team] or 0) + math.ceil(others * (roleData.surviveBonus or 0))
	end

	-- running down the clock must never be beneficial for traitors
	if wintype == WIN_TIMELIMIT then
		local alive_not_traitors = 0
		local dead_not_traitors = 0

		for k, x in pairs(alive) do
			if k ~= TEAM_TRAITOR then
				alive_not_traitors = alive_not_traitors + x
			end
		end

		for k, x in pairs(dead) do
			if k ~= TEAM_TRAITOR then
				dead_not_traitors = dead_not_traitors + x
			end
		end

		local _val = math.floor(alive_not_traitors * -0.5) + math.ceil(dead_not_traitors * 0.5)

		for id, sc in pairs(scores) do
			bonus[id] = (sc.lt == TEAM_TRAITOR) and _val or bonus[id]
		end
	end

	return bonus
end

---
-- Scores were initially calculated as points immediately, but not anymore, so
-- we can convert them using this fn
-- @param table scores scores table
-- @return number kill points
-- @realm shared
function KillsToPoints(score)
	local sc = score.bonus - score.suicides + (score.deaths == 0 and 1 or 0)
	local scoreEv = score.ev

	for i = 1, #scoreEv do
		local ev = scoreEv[i]
		local roleData = roles.GetByIndex(ev.r)

		if ev.t ~= TEAM_NONE and ev.t == ev.v and not TEAMS[ev.t].alone then -- teamkill
			sc = sc + (roleData.scoreTeamKillsMultiplier or 0)
		else -- legit kill
			sc = sc + (roleData.scoreKillsMultiplier or 0)
		end
	end

	return sc
end

-- Weapon AMMO_ enum stuff, used only in score.lua/cl_score.lua these days

-- Not actually ammo identifiers anymore, but still weapon identifiers. Used
-- only in round report (score.lua) to save bandwidth because we can't use
-- pooled strings there. Custom SWEPs are sent as classname string and don't
-- need to bother with these.
AMMO_DEAGLE = 2
AMMO_PISTOL = 3
AMMO_MAC10 = 4
AMMO_RIFLE = 5
AMMO_SHOTGUN = 7

-- Following are custom, intentionally out of ammo enum range
AMMO_CROWBAR = 50
AMMO_SIPISTOL = 51
AMMO_C4 = 52
AMMO_FLARE = 53
AMMO_KNIFE = 54
AMMO_M249 = 55
AMMO_M16 = 56
AMMO_DISCOMB = 57
AMMO_POLTER = 58
AMMO_TELEPORT = 59
AMMO_RADIO = 60
AMMO_DEFUSER = 61
AMMO_WTESTER = 62
AMMO_BEACON = 63
AMMO_HEALTHSTATION = 64
AMMO_MOLOTOV = 65
AMMO_SMOKE = 66
AMMO_BINOCULARS = 67
AMMO_PUSH = 68
AMMO_STUN = 69
AMMO_CSE = 70
AMMO_DECOY = 71
AMMO_GLOCK = 72

local WeaponNames

---
-- Returns a list of @{Weapon} names
-- @return table
-- @realm shared
function GetWeaponClassNames()
	if WeaponNames then
		return WeaponNames
	end

	local tbl = {}
	local weps = weapons.GetList()

	for i = 1, #weps do
		local v = weps[i]

		if v == nil or v.WeaponID == nil then continue end

		tbl[v.WeaponID] = WEPS.GetClass(v)
	end

	for _, v in pairs(scripted_ents.GetList()) do
		local id = istable(v) and (v.WeaponID or (v.t and v.t.WeaponID)) or nil
		if id == nil then continue end

		tbl[id] = WEPS.GetClass(v)
	end

	WeaponNames = tbl

	return WeaponNames
end

---
-- Reverse lookup from enum to SWEP table.
-- Returns a @{Weapon} based on the given ammo
-- @param number ammo
-- @return Weapon
-- @realm shared
function EnumToSWEP(ammo)
	local e2w = GetWeaponClassNames() or {}

	if e2w[ammo] then
		return util.WeaponForClass(e2w[ammo])
	else
		return
	end
end

---
-- Returns a @{Weapon}'s key based on the given ammo
-- @param number ammo
-- @param string key
-- @return any
-- @realm shared
function EnumToSWEPKey(ammo, key)
	local swep = EnumToSWEP(ammo)

	return swep and swep[key]
end

---
-- Something the client can display
-- This used to be done with a big table of AMMO_ ids to names, now we just use
-- the weapon PrintNames. This means it is no longer usable from the server (not
-- used there anyway), and means capitalization is slightly less pretty.
-- @param number ammo
-- @return any same as @{EnumToSWEPKey}
-- @realm shared
-- @see EnumToSWEPKey
function EnumToWep(ammo)
	return EnumToSWEPKey(ammo, "PrintName")
end

---
-- something cheap to send over the network
-- @param Weapon wep
-- @return string the @{Weapon} id
-- @realm shared
function WepToEnum(wep)
	if not IsValid(wep) then return end

	return wep.WeaponID
end
