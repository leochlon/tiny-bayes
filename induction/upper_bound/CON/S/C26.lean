import CON.Groups

/-! Kernel run of the exhaustive search for the groups 104 to 107. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok26 : ∀ c < 108, 104 ≤ c → classOK c = true := by decide +kernel

end S
end CON
