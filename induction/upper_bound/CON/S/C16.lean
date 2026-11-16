import CON.Groups

/-! Kernel run of the exhaustive search for the groups 64 to 67. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok16 : ∀ c < 68, 64 ≤ c → classOK c = true := by decide +kernel

end S
end CON
