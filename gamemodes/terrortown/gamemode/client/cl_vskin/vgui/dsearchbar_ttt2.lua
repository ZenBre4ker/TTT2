---
-- @class PANEL
-- @section DSearchBarTTT2

local PANEL = {}

local font = "DermaTTT2Text"

---
-- @accessor number
-- @realm client
AccessorFunc(PANEL, "heightMult", "HeightMult")

---
-- @accessor bool
-- @realm client
AccessorFunc(PANEL, "isOnFocus", "IsOnFocus")

---
-- @accessor string
-- @realm client
AccessorFunc(PANEL, "placeholderText", "PlaceholderText")

---
-- @accessor string
-- @realm client
AccessorFunc(PANEL, "curPlaceholderText", "CurrentPlaceholderText")

---
-- @ignore
function PANEL:Init()
	local textEntry = vgui.Create("DTextEntry", self)
	local textColor = util.GetActiveColor(util.GetChangedColor(util.GetDefaultColor(vskin.GetBackgroundColor()), 25))

	textEntry:SetFont(font)
	textEntry:SetTextColor(textColor)
	textEntry:SetCursorColor(textColor)

	textEntry.OnValueChange = function(slf,value)
		self:OnValueChange(value)
	end

	textEntry.OnGetFocus = function(slf)
		self:SetIsOnFocus(true)
		self:OnGetFocus()
	end

	textEntry.OnLoseFocus = function(slf)
		self:SetIsOnFocus(false)
		self:OnLoseFocus()

		if slf:GetValue() == "" then
			self:SetCurrentPlaceholderText(self:GetPlaceholderText())
		else
			self:SetCurrentPlaceholderText("")
		end
	end

	-- This turns off the engine drawing for the text entry
	textEntry:SetPaintBackgroundEnabled(false)
	textEntry:SetPaintBorderEnabled(false)
	textEntry:SetPaintBackground(false)

	self.textEntry = textEntry

	-- This turns off the engine drawing of the panel itself
	self:SetPaintBackgroundEnabled(false)
	self:SetPaintBorderEnabled(false)
	self:SetPaintBackground(false)

	-- Sets default values
	self:SetHeightMult(1)
	self:SetIsOnFocus(false)
	self:SetPlaceholderText("searchbar_default_placeholder")
	self:SetCurrentPlaceholderText("searchbar_default_placeholder")

	self:PerformLayout()
end

---
-- This function sets the used font.
-- @param string newFont
-- @realm client
function PANEL:SetFont(newFont)
	self.textEntry:SetFont(newFont)
	font = newFont
end

---
-- This function gets you the current used font.
-- @return string
-- @realm client
function PANEL:GetFont()
	return font
end

---
-- This function gets you the current typed text in the searchbar.
-- @return string
-- @realm client
function PANEL:GetValue()
	return textEntry:GetValue()
end

---
-- This function determines if PANEL:OnValueChange() is called on every typed letter or not.
-- @param bool enabled
-- @realm client
function PANEL:SetUpdateOnType(enabled)
	self.textEntry:SetUpdateOnType(enabled)
end

---
-- This function is called when the searchbar is focussed.
-- You can overwrite this with your own function.
-- @realm client
function PANEL:OnGetFocus()
end

---
-- This function is called when the searchbar is not focussed anymore.
-- You can overwrite this with your own function.
-- @realm client
function PANEL:OnLoseFocus()
end

---
-- This function is called by the searchbar when a text is entered/changed.
-- You can overwrite this with your own function.
-- @param string value
-- @realm client
function PANEL:OnValueChange(value)
end

---
-- @ignore
function PANEL:Paint(w, h)
	derma.SkinHook("Paint", "Searchbar", self, w, h)

	return true
end

---
-- @ignore
function PANEL:PerformLayout()
	local width, height = self:GetSize()
	local heightMult = self:GetHeightMult()

	self.textEntry:SetSize(width, height * heightMult)
	self.textEntry:SetPos(0, height * (1 - heightMult) / 2)

	self.textEntry:InvalidateLayout(true)
end

---
-- @return boolean
-- @realm client
function PANEL:Clear()
	return self.textEntry:Clear()
end

derma.DefineControl("DSearchBarTTT2", "", PANEL, "DPanelTTT2")
