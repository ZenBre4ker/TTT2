--- @ignore

if CLIENT then
	--EVENT.icon = nil
	EVENT.title = "title_event_c4_explode"

	function EVENT:GetText()
		return {
			{
				string = "desc_event_c4_explode",
				params = {
					owner = self.event.owner.nick,
					role = roles.GetByIndex(self.event.owner.role).name,
					team = self.event.owner.team
				},
				translateParams = true
			}
		}
	end
end

if SERVER then
	function EVENT:Trigger(owner)
		self:AddAffectedPlayers({owner:SteamID64()})

		return self:Add({
			nick = owner:Nick(),
			sid64 = owner:SteamID64(),
			role = owner:GetSubRole(),
			team = owner:GetTeam()
		})
	end
end

function EVENT:GetDeprecatedFormat()
	local event = self.event

	if event.roundState ~= ROUND_ACTIVE then return end

	return {
		id = self.type,
		t = event.time / 1000,
		ni = event.nick,
	}
end
