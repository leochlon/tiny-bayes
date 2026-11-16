import CON.Groups

/-! Kernel run of the exhaustive search for the groups 32 to 35. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok8 : ∀ c < 36, 32 ≤ c → classOK c = true := by decide +kernel

end S
end CON
