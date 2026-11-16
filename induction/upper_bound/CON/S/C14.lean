import CON.Groups

/-! Kernel run of the exhaustive search for the groups 56 to 59. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok14 : ∀ c < 60, 56 ≤ c → classOK c = true := by decide +kernel

end S
end CON
