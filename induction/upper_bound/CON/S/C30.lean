import CON.Groups

/-! Kernel run of the exhaustive search for the groups 120 to 123. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok30 : ∀ c < 124, 120 ≤ c → classOK c = true := by decide +kernel

end S
end CON
