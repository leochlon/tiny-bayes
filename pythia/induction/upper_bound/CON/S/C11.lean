import CON.Groups

/-! Kernel run of the exhaustive search for the groups 44 to 47. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok11 : ∀ c < 48, 44 ≤ c → classOK c = true := by decide +kernel

end S
end CON
