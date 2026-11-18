import CON.Groups

/-! Kernel run of the exhaustive search for the groups 112 to 115. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok28 : ∀ c < 116, 112 ≤ c → classOK c = true := by decide +kernel

end S
end CON
