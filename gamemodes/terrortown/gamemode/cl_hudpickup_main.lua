local TryTranslation = LANG.TryTranslation

GM.PickupHistory = {}
GM.PickupHistoryLast = 0
GM.PickupHistoryTop = ScrH() * 0.5
GM.PickupHistoryWide = 300
GM.PickupHistoryCorner = surface.GetTextureID("gui/corner8")

function GM:HUDWeaponPickedUp(wep)
	if not IsValid(wep) then return end

	local client = LocalPlayer()

	if not IsValid(client) or not client:Alive() then return end

	local name = GetEquipmentTranslation(wep:GetClass(), (wep.GetPrintName and wep:GetPrintName()) or wep:GetClass())
	--local name = TryTranslation(wep.GetPrintName and wep:GetPrintName() or wep:GetClass() or "Unknown Weapon Name")

	local pickup = {}
	pickup.time = CurTime()
	pickup.name = string.upper(name)
	pickup.holdtime = 5
	pickup.font = "DefaultBold"
	pickup.fadein = 0.04
	pickup.fadeout = 0.3

	local subrole = client.GetSubRole and client:GetSubRole() or ROLE_INNOCENT

	pickup.color = GetRoleByIndex(subrole).color
	pickup.upper = true

	surface.SetFont(pickup.font)

	local w, h = surface.GetTextSize(pickup.name)

	pickup.height = h
	pickup.width = w

	if self.PickupHistoryLast >= pickup.time then
		pickup.time = self.PickupHistoryLast + 0.05
	end

	table.insert(self.PickupHistory, pickup)

	self.PickupHistoryLast = pickup.time
end

function GM:HUDItemPickedUp(itemname)
	local client = LocalPlayer()

	if not IsValid(client) or not client:Alive() then return end

	local pickup = {}
	pickup.time = CurTime()
	-- as far as I'm aware TTT does not use any "items", so better leave this to
	-- source's localisation
	pickup.name = "#" .. itemname
	pickup.holdtime = 5
	pickup.font = "DefaultBold"
	pickup.fadein = 0.04
	pickup.fadeout = 0.3
	pickup.color = Color(255, 255, 255, 255)
	pickup.upper = false

	surface.SetFont(pickup.font)

	local w, h = surface.GetTextSize(pickup.name)

	pickup.height = h
	pickup.width = w

	if self.PickupHistoryLast >= pickup.time then
		pickup.time = self.PickupHistoryLast + 0.05
	end

	table.insert(self.PickupHistory, pickup)

	self.PickupHistoryLast = pickup.time
end

function GM:HUDAmmoPickedUp(itemname, amount)
	local client = LocalPlayer()

	if not IsValid(client) or not client:Alive() then return end

	local itemname_trans = TryTranslation(string.lower("ammo_" .. itemname))

	if self.PickupHistory then
		local localized_name = string.upper(itemname_trans)

		for _, v in pairs(self.PickupHistory) do
			if v.name == localized_name then
				v.amount = tostring(tonumber(v.amount) + amount)
				v.time = CurTime() - v.fadein

				return
			end
		end
	end

	local pickup = {}
	pickup.time = CurTime()
	pickup.name = string.upper(itemname_trans)
	pickup.holdtime = 5
	pickup.font = "DefaultBold"
	pickup.fadein = 0.04
	pickup.fadeout = 0.3
	pickup.color = Color(205, 155, 0, 255)
	pickup.amount = tostring(amount)

	surface.SetFont(pickup.font)

	local w, h = surface.GetTextSize(pickup.name)

	pickup.height = h
	pickup.width = w

	w, h = surface.GetTextSize(pickup.amount)

	pickup.width = pickup.width + w + 16

	if self.PickupHistoryLast >= pickup.time then
		pickup.time = self.PickupHistoryLast + 0.05
	end

	table.insert(self.PickupHistory, pickup)

	self.PickupHistoryLast = pickup.time
end

function GM:HUDDrawPickupHistory()
	if not self.PickupHistory then return end

	local x, y = ScrW() - self.PickupHistoryWide - 20, self.PickupHistoryTop
	local tall = 0
	local wide = 0

	for k, v in pairs(self.PickupHistory) do
		if v.time < CurTime() then
			v.y = v.y or y
			v.y = (v.y * 5 + y) / 6

			local alpha = 255
			local delta = (v.time + v.holdtime - CurTime()) / v.holdtime
			local colordelta = math.Clamp(delta, 0.6, 0.7)

			if delta > 1 - v.fadein then
				alpha = math.Clamp((1.0 - delta) * (255 / v.fadein), 0, 255)
			elseif delta < v.fadeout then
				alpha = math.Clamp(delta * (255 / v.fadeout), 0, 255)
			end

			v.x = x + self.PickupHistoryWide - self.PickupHistoryWide * (alpha / 255)

			local rx, ry, rw, rh = math.Round(v.x - 4), math.Round(v.y - v.height * 0.5 - 4), math.Round(self.PickupHistoryWide + 9), math.Round(v.height + 8)
			local bordersize = 8

			surface.SetTexture(self.PickupHistoryCorner)

			surface.SetDrawColor(v.color.r, v.color.g, v.color.b, alpha)
			surface.DrawTexturedRectRotated(rx + bordersize * 0.5, ry + bordersize * 0.5, bordersize, bordersize, 0)
			surface.DrawTexturedRectRotated(rx + bordersize * 0.5, ry + rh - bordersize * 0.5, bordersize, bordersize, 90)
			surface.DrawRect(rx, ry + bordersize, bordersize, rh - bordersize * 2)
			surface.DrawRect(rx + bordersize, ry, v.height - 4, rh)

			surface.SetDrawColor(20 * colordelta, 20 * colordelta, 20 * colordelta, math.Clamp(alpha, 0, 200))
			surface.DrawRect(rx + bordersize + v.height - 4, ry, rw - (v.height - 4) - bordersize * 2, rh)
			surface.DrawTexturedRectRotated(rx + rw - bordersize * 0.5, ry + rh - bordersize * 0.5, bordersize, bordersize, 180)
			surface.DrawTexturedRectRotated(rx + rw - bordersize * 0.5, ry + bordersize * 0.5, bordersize, bordersize, 270)
			surface.DrawRect(rx + rw - bordersize, ry + bordersize, bordersize, rh - bordersize * 2)

			draw.SimpleText(v.name, v.font, v.x + 2 + v.height + 8, v.y - v.height * 0.5 + 2, Color(0, 0, 0, alpha * 0.75))
			draw.SimpleText(v.name, v.font, v.x + v.height + 8, v.y - v.height * 0.5, Color(255, 255, 255, alpha))

			if v.amount then
				draw.SimpleText(v.amount, v.font, v.x + self.PickupHistoryWide + 2, v.y - v.height * 0.5 + 2, Color(0, 0, 0, alpha * 0.75), TEXT_ALIGN_RIGHT)
				draw.SimpleText(v.amount, v.font, v.x + self.PickupHistoryWide, v.y - v.height * 0.5, Color(255, 255, 255, alpha), TEXT_ALIGN_RIGHT)
			end

			y = y + v.height + 16
			tall = tall + v.height + 18
			wide = math.Max(wide, v.width + v.height + 24)

			if alpha == 0 then
				self.PickupHistory[k] = nil
			end
		end
	end

	self.PickupHistoryTop = (self.PickupHistoryTop * 5 + (ScrH() * 0.75 - tall) * 0.5) / 6
	self.PickupHistoryWide = (self.PickupHistoryWide * 5 + wide) / 6
end
