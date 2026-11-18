import CON.Groups

/-! Kernel run of the exhaustive search for the groups 160 to 163. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok40 : ∀ c < 164, 160 ≤ c → classOK c = true := by decide +kernel

end S
end CON
