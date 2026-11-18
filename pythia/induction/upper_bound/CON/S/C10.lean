import CON.Groups

/-! Kernel run of the exhaustive search for the groups 40 to 43. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok10 : ∀ c < 44, 40 ≤ c → classOK c = true := by decide +kernel

end S
end CON
