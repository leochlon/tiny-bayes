import CON.Groups

/-! Kernel run of the exhaustive search for the groups 124 to 127. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok31 : ∀ c < 128, 124 ≤ c → classOK c = true := by decide +kernel

end S
end CON
