import CON.Groups

/-! Kernel run of the exhaustive search for the groups 100 to 103. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok25 : ∀ c < 104, 100 ≤ c → classOK c = true := by decide +kernel

end S
end CON
