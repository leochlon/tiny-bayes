import CON.Groups

/-! Kernel run of the exhaustive search for the groups 156 to 159. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok39 : ∀ c < 160, 156 ≤ c → classOK c = true := by decide +kernel

end S
end CON
