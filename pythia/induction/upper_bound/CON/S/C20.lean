import CON.Groups

/-! Kernel run of the exhaustive search for the groups 80 to 83. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok20 : ∀ c < 84, 80 ≤ c → classOK c = true := by decide +kernel

end S
end CON
