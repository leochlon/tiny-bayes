import CON.Groups

/-! Kernel run of the exhaustive search for the groups 60 to 63. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok15 : ∀ c < 64, 60 ≤ c → classOK c = true := by decide +kernel

end S
end CON
