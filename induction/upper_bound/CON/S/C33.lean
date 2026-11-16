import CON.Groups

/-! Kernel run of the exhaustive search for the groups 132 to 135. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok33 : ∀ c < 136, 132 ≤ c → classOK c = true := by decide +kernel

end S
end CON
