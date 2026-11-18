import CON.Groups

/-! Kernel run of the exhaustive search for the groups 16 to 19. -/

namespace CON
namespace S

set_option maxRecDepth 100000 in
theorem ok4 : ∀ c < 20, 16 ≤ c → classOK c = true := by decide +kernel

end S
end CON
