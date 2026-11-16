import CON.Groups

/-! Kernel run of the exhaustive search for the groups 152 to 155. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok38 : ∀ c < 156, 152 ≤ c → classOK c = true := by decide +kernel

end S
end CON
