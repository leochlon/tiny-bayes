import CON.Groups

/-! Kernel run of the exhaustive search for the groups 84 to 87. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok21 : ∀ c < 88, 84 ≤ c → classOK c = true := by decide +kernel

end S
end CON
