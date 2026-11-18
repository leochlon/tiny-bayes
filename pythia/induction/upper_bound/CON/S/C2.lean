import CON.Groups

/-! Kernel run of the exhaustive search for the groups 8 to 11. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok2 : ∀ c < 12, 8 ≤ c → classOK c = true := by decide +kernel

end S
end CON
