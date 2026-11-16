import CON.Groups

/-! Kernel run of the exhaustive search for the groups 36 to 39. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok9 : ∀ c < 40, 36 ≤ c → classOK c = true := by decide +kernel

end S
end CON
