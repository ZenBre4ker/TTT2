---
-- This is the map module to have some short access functions
-- @author Mineotopia
-- @module map

if SERVER then
	AddCSLuaFile()
end

local scripedEntsRegister = scripted_ents.Register

local pairs = pairs

local mapType = nil

local fallbackWepSpawnEnts = {
	-- CS:S
	"hostage_entity",
	-- TF2
	"item_ammopack_full",
	"item_ammopack_medium",
	"item_ammopack_small",
	"item_healthkit_full",
	"item_healthkit_medium",
	"item_healthkit_small",
	"item_teamflag",
	"game_intro_viewpoint",
	"info_observer_point",
	"team_control_point",
	"team_control_point_master",
	"team_control_point_round",
	-- ZM
	"item_ammo_revolver"
}

local ttt_weapon_spawns = {
	["ttt_random_weapon"] = WEAPON_TYPE_RANDOM,
	["weapon_zm_shotgun"] = WEAPON_TYPE_SHOTGUN,
	["weapon_zm_pistol"] = WEAPON_TYPE_PISTOL,
	["weapon_zm_rifle"] = WEAPON_TYPE_SNIPER,
	["weapon_zm_molotov"] = WEAPON_TYPE_NADE,
	["weapon_ttt_smokegrenade"] = WEAPON_TYPE_NADE,
	["weapon_ttt_confgrenade"] = WEAPON_TYPE_NADE,
	["weapon_zm_mac10"] = WEAPON_TYPE_ASSAULT,
	["weapon_zm_revolver"] = WEAPON_TYPE_PISTOL,
	["weapon_zm_sledge"] = WEAPON_TYPE_ASSAULT,
	["weapon_ttt_m16"] = WEAPON_TYPE_ASSAULT,
	["weapon_ttt_glock"] = WEAPON_TYPE_PISTOL
}

local ttt_ammo_spawns = {
	["ttt_random_ammo"] = AMMO_TYPE_RANDOM,
	["item_ammo_pistol_ttt"] = AMMO_TYPE_PISTOL,
	["item_ammo_smg1_ttt"] = AMMO_TYPE_MAC10,
	["item_ammo_357_ttt"] = AMMO_TYPE_RIFLE,
	["item_box_buckshot_ttt"] = AMMO_TYPE_SHOTGUN,
	["item_ammo_revolver_ttt"] = AMMO_TYPE_DEAGLE
}

local hl2_weapon_spawns = {
	["weapon_smg1"] = WEAPON_TYPE_ASSAULT,
	["weapon_shotgun"] = WEAPON_TYPE_SHOTGUN,
	["weapon_ar2"] = WEAPON_TYPE_ASSAULT,
	["weapon_357"] = WEAPON_TYPE_SNIPER,
	["weapon_crossbow"] = WEAPON_TYPE_PISTOL,
	["weapon_rpg"] = WEAPON_TYPE_ASSAULT,
	["weapon_frag"] = WEAPON_TYPE_PISTOL,
	["weapon_crowbar"] = WEAPON_TYPE_NADE,
	["item_ammo_smg1_grenade"] = WEAPON_TYPE_PISTOL,
	["item_healthkit"] = WEAPON_TYPE_SHOTGUN,
	["item_suitcharger"] = WEAPON_TYPE_ASSAULT,
	["item_ammo_ar2_altfire"] = WEAPON_TYPE_ASSAULT,
	["item_healthvial"] = WEAPON_TYPE_NADE,
	["item_ammo_crate"] = WEAPON_TYPE_NADE
}

local hl2_ammo_spawns = {
	["weapon_slam"] = AMMO_TYPE_PISTOL,
	["item_ammo_pistol"] = AMMO_TYPE_PISTOL,
	["item_box_buckshot"] = AMMO_TYPE_SHOTGUN,
	["item_ammo_smg1"] = AMMO_TYPE_MAC10,
	["item_ammo_357"] = AMMO_TYPE_RIFLE,
	["item_ammo_357_large"] = AMMO_TYPE_RIFLE,
	["item_ammo_revolver"] = AMMO_TYPE_DEAGLE, -- zm
	["item_ammo_ar2"] = AMMO_TYPE_PISTOL,
	["item_ammo_ar2_large"] = AMMO_TYPE_MAC10,
	["item_battery"] = AMMO_TYPE_RIFLE,
	["item_rpg_round"] = AMMO_TYPE_RIFLE,
	["item_ammo_crossbow"] = AMMO_TYPE_SHOTGUN,
	["item_healthcharger"] = AMMO_TYPE_DEAGLE,
	["item_item_crate"] = AMMO_TYPE_RANDOM
}

local css_weapon_spawns = {
	["info_player_terrorist"] = WEAPON_TYPE_RANDOM,
	["info_player_counterterrorist"] = WEAPON_TYPE_RANDOM,
	["hostage_entity"] = WEAPON_TYPE_RANDOM
}

local tf2_weapon_spawns = {
	["info_player_teamspawn"] = WEAPON_TYPE_RANDOM,
	["team_control_point"] = WEAPON_TYPE_RANDOM,
	["team_control_point_master"] = WEAPON_TYPE_RANDOM,
	["team_control_point_round"] = WEAPON_TYPE_RANDOM,
	["item_ammopack_full"] = WEAPON_TYPE_RANDOM,
	["item_ammopack_medium"] = WEAPON_TYPE_RANDOM,
	["item_ammopack_small"] = WEAPON_TYPE_RANDOM,
	["item_healthkit_full"] = WEAPON_TYPE_RANDOM,
	["item_healthkit_medium"] = WEAPON_TYPE_RANDOM,
	["item_healthkit_small"] = WEAPON_TYPE_RANDOM,
	["item_teamflag"] = WEAPON_TYPE_RANDOM,
	["game_intro_viewpoint"] = WEAPON_TYPE_RANDOM,
	["info_observer_point"] = WEAPON_TYPE_RANDOM
}

local function FindSpawns(spawns, classes)
	for class, entType in pairs(classes) do
		local weps = ents.FindByClass(class)

		for i = 1, #weps do
			local wep = weps[i]

			spawns[entType] = spawns[entType] or {}

			spawns[entType][#spawns[entType] + 1] = {
				pos = wep:GetPos(),
				ang = wep:GetAngles()
			}
		end
	end
end

map = map or {}

MAP_TYPE_TERRORTOWN = 1
MAP_TYPE_COUNTERSTRIKE = 2
MAP_TYPE_TEAMFORTRESS = 3

---
-- CS:S and TF2 maps have a bunch of ents we'd like to abuse for weapon spawns,
-- but to do that we need to register a SENT with their class name, else they
-- will just error out and we can't do anything with them.
-- @internal
-- @realm server
function map.DummifyFallbackWeaponEnts()
	for i = 1, #fallbackWepSpawnEnts do
		scripedEntsRegister({
			Type = "point",
			IsWeaponDummy = true
		}, fallbackWepSpawnEnts[i], false)
	end
end

-- automatically run the dummmify function
map.DummifyFallbackWeaponEnts()

---
-- Returns the exptected type of the current map.
-- @note This function uses caching to improve performance and only reads the
-- map entities on the first call of the funciton.
-- @return[default=MAP_TYPE_TERRORTOWN] number Returns the map type of the currently active map
-- @realm shared
function map.GetMapGameType()
	-- return cached map type if already cached
	if mapType then
		return mapType
	end

	if #ents.FindByClass("info_player_counterterrorist") ~= 0 then
		mapType = MAP_TYPE_COUNTERSTRIKE
	elseif #ents.FindByClass("info_player_teamspawn") ~= 0 then
		mapType = MAP_TYPE_TEAMFORTRESS
	else
		-- as a fallback use the terrortown map type since most maps are terrotown maps;
		-- they are identified with the class 'info_player_deathmatch'
		mapType = MAP_TYPE_TERRORTOWN
	end

	return mapType
end

---
-- Checks if the currently selected map is a terrortown map.
-- @note This function uses caching to improve performance and only reads the
-- map entities on the first call of the funciton.
-- @return boolean Returns true if it is a terrortown map
-- @realm shared
function map.IsTerrortownMap()
	return map.GetMapGameType() == MAP_TYPE_TERRORTOWN
end

---
-- Checks if the currently selected map is a counter strike source map.
-- @note This function uses caching to improve performance and only reads the
-- map entities on the first call of the funciton.
-- @return boolean Returns true if it is a counter strike source map
-- @realm shared
function map.IsCounterStrikeMap()
	return map.GetMapGameType() == MAP_TYPE_COUNTERSTRIKE
end

---
-- Checks if the currently selected map is a team fortress 2 map.
-- @note This function uses caching to improve performance and only reads the
-- map entities on the first call of the funciton.
-- @return boolean Returns true if it is a team fortress 2 map
-- @realm shared
function map.IsTeamFortressMap()
	return map.GetMapGameType() == MAP_TYPE_TEAMFORTRESS
end

function map.GetWeaponSpawnEntities()
	local spawns = {}

	FindSpawns(spawns, ttt_weapon_spawns)
	FindSpawns(spawns, hl2_weapon_spawns)

	if map.IsCounterStrikeMap() then
		FindSpawns(spawns, css_weapon_spawns)
	elseif map.IsTeamFortressMap() then
		FindSpawns(spawns, tf2_weapon_spawns)
	end

	return spawns
end

function map.GetAmmoSpawnEntities()
	local spawns = {}

	FindSpawns(spawns, ttt_ammo_spawns)
	FindSpawns(spawns, hl2_ammo_spawns)

	return spawns
end