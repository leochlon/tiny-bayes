import CON.Groups

/-! Kernel run of the exhaustive search for the groups 140 to 143. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok35 : ∀ c < 144, 140 ≤ c → classOK c = true := by decide +kernel

end S
end CON
