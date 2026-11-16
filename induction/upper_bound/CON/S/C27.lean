import CON.Groups

/-! Kernel run of the exhaustive search for the groups 108 to 111. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok27 : ∀ c < 112, 108 ≤ c → classOK c = true := by decide +kernel

end S
end CON
