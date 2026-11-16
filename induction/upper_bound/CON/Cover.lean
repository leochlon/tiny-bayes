import Mathlib
import CON.Groups

/-! Every token of `V` is the entry of `groups` that the table assigns to it (kernel computation). -/

namespace CON

theorem cover : ∀ x ∈ V, posOf x < (groups.getD (cls x) []).length ∧
    (groups.getD (cls x) []).getD (posOf x) 0 = x := by decide +kernel

end CON
