import CON.Groups

/-! Kernel run of the exhaustive search for the groups 4 to 7. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok1 : ∀ c < 8, 4 ≤ c → classOK c = true := by decide +kernel

end S
end CON
