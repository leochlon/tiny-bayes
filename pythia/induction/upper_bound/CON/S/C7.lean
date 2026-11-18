import CON.Groups

/-! Kernel run of the exhaustive search for the groups 28 to 31. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok7 : ∀ c < 32, 28 ≤ c → classOK c = true := by decide +kernel

end S
end CON
