import CON.Groups

/-! Kernel run of the exhaustive search for the groups 92 to 95. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok23 : ∀ c < 96, 92 ≤ c → classOK c = true := by decide +kernel

end S
end CON
