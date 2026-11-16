import CON.Groups

/-! Kernel run of the exhaustive search for the groups 68 to 71. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok17 : ∀ c < 72, 68 ≤ c → classOK c = true := by decide +kernel

end S
end CON
