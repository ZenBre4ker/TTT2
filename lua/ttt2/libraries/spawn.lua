---
-- A load of function handling player spawn
-- @author Mineotopia
-- @module spawn

if CLIENT then return end -- this is a serverside-ony module

local Vector = Vector
local table = table
local mathSin = math.sin
local mathCos = math.cos

local spawnPointVariations = {Vector(0, 0, 0)}

for i = 0, 360, 22.5 do
	spawnPointVariations[#spawnPointVariations + 1] = Vector(mathCos(i), mathSin(i), 0)
end

-- returns the player size as a vector
local function GetPlayerSize(ply)
	local bottom, top = ply:GetHull()

	return top - bottom
end

spawn = spawn or {}

---
-- Checks if a given spawn point is safe. Safe means that a player can spawn without
-- being stuck. Entities which are passable are ignored by the check.
-- @param Player ply The player entity that should spawn, this parameter is needed
-- to make sure there is enough space for this specific playermodel.
-- @param Vector pos The respawn position
-- @param[default=false] boolean force Should the respawn be forced? This means killing other players that block this position
-- @param[opt] table|Entity filter A table of entities or an entity that should be ignored by this check
-- @return boolean Returns if the spawn point is safe
-- @realm server
function spawn.IsSpawnPointSafe(ply, pos, force, filter)
	local sizePlayer = GetPlayerSize(ply)

	if not util.IsInWorld(pos) then
		return false
	end

	filter = istable(filter) and filter or {filter}

	-- the center pos is slightly shifted to the top to prevent ground
	-- collisions in the walltrace
	local posCenter = pos + Vector(0, 0, 0.525 * sizePlayer.z)

	-- Make sure there is enough space around the player
	local traceWalls = util.TraceHull({
		start = posCenter,
		endpos = posCenter,
		mins = -0.5 * sizePlayer,
		maxs = 0.5 * sizePlayer,
		filter = function(ent)
			if not IsValid(ent) or table.HasValue(filter, ent) then
				return false
			end

			if ent:HasPassableCollisionGrup() then
				return false
			end

			return true
		end,
		mask = MASK_SOLID
	})

	if traceWalls.Hit then
		return false
	end

	-- make sure the new position is on the ground
	local traceGround = util.TraceLine({
		start = posCenter,
		endpos = posCenter - Vector(0, 0, sizePlayer.z),
		filter = player.GetAll(),
		mask = MASK_SOLID
	})

	if not traceGround.Hit then
		return false
	end

	local blockingEntities = ents.FindInBox(
		pos + Vector(-0.5 * sizePlayer.x, -0.5 * sizePlayer.y, 0),
		pos + sizePlayer
	)

	for i = 1, #blockingEntities do
		local blockingEntity = blockingEntities[i]

		if not IsValid(blockingEntity) or not blockingEntity:IsPlayer()
			or not blockingEntity:IsTerror() or not blockingEntity:Alive()
		then continue end

		if table.HasValue(filter, blockingEntity) then continue end

		if force then
			blockingEntity:Kill()
		else
			return false
		end
	end

	return true
end

---
-- Returns a selection of points around the given position.
-- @param Player ply The player entity that should spawn, this parameter is needed
-- to make sure there is enough space for this specific playermodel.
-- @param Vector pos The given position
-- @param[default=1] number radiusMultiplier The radius multiplayer to calculate the new positions
-- @return table A table of position vectors
-- @realm server
function spawn.GetSpawnPointsAroundSpawn(ply, pos, radiusMultiplier)
	local sizePlayer = GetPlayerSize(ply)

	if not pos then return {} end

	local boundsPlayer = Vector(sizePlayer.x, sizePlayer.y, 0) * 1.5 * (radiusMultiplier or 1)
	local positions = {}

	for i = 1, #spawnPointVariations do
		positions[i] = pos + spawnPointVariations[i] * boundsPlayer
	end

	return positions
end

---
-- Tries to make spawn position valid by scanning surrounding area for
-- valid positions.
-- @param Player ply The player entity that should spawn, this parameter is needed
-- to make sure there is enough space for this specific playermodel.
-- @param Vector unsafePos The unsafe spawn position
-- @param[default=1] number radiusMultiplier The radius multiplayer to calculate the new positions
-- @return Vector|nil Returns the safe spawn position, nil if none was found
-- @realm server
function spawn.MakeSpawnPointSafe(ply, unsafePos, radiusMultiplier)
	local spawnPoints = spawn.GetSpawnPointsAroundSpawn(ply, unsafePos, radiusMultiplier)

	for i = 1, #spawnPoints do
		local spawnPoint = spawnPoints[i]

		if not spawn.IsSpawnPointSafe(ply, spawnPoint, false) then continue end

		return spawnPoint
	end
end

---
-- Returns a list of all spawn entities found on the map that are valid to spawn players.
-- @warning Don't use 'info_player_start' unless absolutely necessary, because eg. TF2 uses
-- it for observer starts that are in places where players cannot really spawn well.
-- Therefore by default 'info_player_start' is not included in the search. However if 'forceAll'
-- is set to true or no other map spawn was found, these spawn entities will be included.
-- @deprecated Use @{map.GetPlayerSpawnEntities} instead
-- @return table Returns a table of unsafe spawn entities
-- @realm server
function spawn.GetPlayerSpawnEntities()
	return entspawnscript.GetSpawnEntitiesForSpawnType(SPAWN_TYPE_PLAYER)[PLAYER_TYPE_RANDOM]
end

---
-- Gets a table of spawnpoints on the map.
-- @note These spawn points are not shuffled.
-- @return table Returns a table of spawnpoints as @{Vector}s
-- @realm server
function spawn.GetPlayerSpawnPointTable()
	local spawnEnts = spawn.GetPlayerSpawnEntities()
	local spawnPoints = {}

	for i = 1, #spawnEnts do
		spawnPoints[i] = spawnEnts[i]:GetPos()
	end

	return spawnPoints
end

---
-- Gets a safe random player spawn entity. If no free and safe spawnpoint is found, it tries
-- to create its own by searching around existing ones.
-- @param Player ply The player that should receive their spawn point
-- @return Entity A safe spawn entity
-- @realm server
function spawn.GetRandomPlayerSpawnEntity(ply)
	local spawnEntities = spawn.GetPlayerSpawnEntities()

	if #spawnEntities == 0 then
		Error("No spawn entity found!\n")

		return
	end

	-- the table should be shuffled for each spawn point calculation to improve randomness
	table.Shuffle(spawnEntities)

	if not IsValid(ply) or not ply:IsTerror() then
		local spawnEnt = ents.Create("info_player_terrorist")

		spawnEnt:SetPos(spawnEntities[1].pos)
		spawnEnt:SetAngles(spawnEntities[1].ang)

		return spawnEnt
	end

	-- Optimistic attempt: assume there are sufficient spawns for all and one is free
	for i = 1, #spawnEntities do
		local spawnEntity = spawnEntities[i]

		if not spawn.IsSpawnPointSafe(ply, spawnEntity.pos, false) then continue end

		local spawnEnt = ents.Create("info_player_terrorist")

		spawnEnt:SetPos(spawnEntity.pos)
		spawnEnt:SetAngles(spawnEntity.ang)

		return spawnEnt
	end

	-- That did not work, so now look around spawns
	local pickedSpawnEntity

	for i = 1, #spawnEntities do
		pickedSpawnEntity = spawnEntities[i]

		local riggedSpawnPoint = spawn.MakeSpawnPointSafe(ply, pickedSpawnEntity.pos)

		if not riggedSpawnPoint then continue end

		local riggedSpawnEntity = ents.Create("info_player_terrorist")

		riggedSpawnEntity:SetPos(riggedSpawnPoint)
		riggedSpawnEntity:SetAngles(pickedSpawnEntity.ang)
		riggedSpawnEntity:Spawn()

		ErrorNoHalt("TTT2 WARNING: Map has too few spawn points, using a riggedSpawnPoints spawn for " .. tostring(ply) .. "\n")

		-- this is an old TTT flag that I will keep for compatibilities sake
		GAMEMODE.HaveRiggedSpawn = true

		return riggedSpawnEntity
	end

	-- Last attempt, force one
	for i = 1, #spawnEntities do
		local spawnEntity = spawnEntities[i]

		if not spawn.IsSpawnPointSafe(ply, spawnEntity.pos, true) then continue end

		local spawnEnt = ents.Create("info_player_terrorist")

		spawnEnt:SetPos(spawnEntity.pos)
		spawnEnt:SetAngles(spawnEntity.ang)

		return spawnEnt
	end

	local spawnEnt = ents.Create("info_player_terrorist")

	spawnEnt:SetPos(pickedSpawnEntity.pos)
	spawnEnt:SetAngles(pickedSpawnEntity.ang)

	return spawnEnt
end
