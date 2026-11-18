import CON.Groups

/-! Kernel run of the exhaustive search for the groups 72 to 75. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok18 : ∀ c < 76, 72 ≤ c → classOK c = true := by decide +kernel

end S
end CON
