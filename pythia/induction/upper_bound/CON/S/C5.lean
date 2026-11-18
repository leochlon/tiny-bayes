import CON.Groups

/-! Kernel run of the exhaustive search for the groups 20 to 23. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok5 : ∀ c < 24, 20 ≤ c → classOK c = true := by decide +kernel

end S
end CON
