import CON.Groups

/-! Kernel run of the exhaustive search for the groups 116 to 119. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok29 : ∀ c < 120, 116 ≤ c → classOK c = true := by decide +kernel

end S
end CON
