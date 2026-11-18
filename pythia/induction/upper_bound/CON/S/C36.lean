import CON.Groups

/-! Kernel run of the exhaustive search for the groups 144 to 147. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok36 : ∀ c < 148, 144 ≤ c → classOK c = true := by decide +kernel

end S
end CON
