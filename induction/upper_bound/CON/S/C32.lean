import CON.Groups

/-! Kernel run of the exhaustive search for the groups 128 to 131. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok32 : ∀ c < 132, 128 ≤ c → classOK c = true := by decide +kernel

end S
end CON
