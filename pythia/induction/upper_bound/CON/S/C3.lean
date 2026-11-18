import CON.Groups

/-! Kernel run of the exhaustive search for the groups 12 to 15. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok3 : ∀ c < 16, 12 ≤ c → classOK c = true := by decide +kernel

end S
end CON
