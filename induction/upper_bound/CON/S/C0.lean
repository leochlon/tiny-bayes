import CON.Groups

/-! Kernel run of the exhaustive search for the groups 0 to 3. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok0 : ∀ c < 4, 0 ≤ c → classOK c = true := by decide +kernel

end S
end CON
