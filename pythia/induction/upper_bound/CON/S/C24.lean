import CON.Groups

/-! Kernel run of the exhaustive search for the groups 96 to 99. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok24 : ∀ c < 100, 96 ≤ c → classOK c = true := by decide +kernel

end S
end CON
