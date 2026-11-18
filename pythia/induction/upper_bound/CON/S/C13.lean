import CON.Groups

/-! Kernel run of the exhaustive search for the groups 52 to 55. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok13 : ∀ c < 56, 52 ≤ c → classOK c = true := by decide +kernel

end S
end CON
