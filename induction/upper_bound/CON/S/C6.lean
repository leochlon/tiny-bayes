import CON.Groups

/-! Kernel run of the exhaustive search for the groups 24 to 27. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok6 : ∀ c < 28, 24 ≤ c → classOK c = true := by decide +kernel

end S
end CON
