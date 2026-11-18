import CON.Groups

/-! Kernel run of the exhaustive search for the groups 136 to 139. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok34 : ∀ c < 140, 136 ≤ c → classOK c = true := by decide +kernel

end S
end CON
