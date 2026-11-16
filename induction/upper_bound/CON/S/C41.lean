import CON.Groups

/-! Kernel run of the exhaustive search for the groups 164 to 166. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok41 : ∀ c < 167, 164 ≤ c → classOK c = true := by decide +kernel

end S
end CON
