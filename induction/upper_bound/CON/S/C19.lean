import CON.Groups

/-! Kernel run of the exhaustive search for the groups 76 to 79. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok19 : ∀ c < 80, 76 ≤ c → classOK c = true := by decide +kernel

end S
end CON
