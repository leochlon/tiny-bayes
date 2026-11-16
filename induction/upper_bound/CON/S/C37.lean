import CON.Groups

/-! Kernel run of the exhaustive search for the groups 148 to 151. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok37 : ∀ c < 152, 148 ≤ c → classOK c = true := by decide +kernel

end S
end CON
