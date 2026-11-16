import CON.Groups

/-! Kernel run of the exhaustive search for the groups 88 to 91. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok22 : ∀ c < 92, 88 ≤ c → classOK c = true := by decide +kernel

end S
end CON
