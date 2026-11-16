import CON.Groups

/-! Kernel run of the exhaustive search for the groups 48 to 51. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok12 : ∀ c < 52, 48 ≤ c → classOK c = true := by decide +kernel

end S
end CON
