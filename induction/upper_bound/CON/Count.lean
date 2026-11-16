import Mathlib
import CON.Groups

/-! The number of instances of the explicit certificate (kernel computation). -/

namespace CON

/-- The number of triples of positions `i < j < l < n` whose bit in `mask` is clear. -/
def clearCount (mask n : ℕ) : ℕ :=
  ((List.range n).map fun l => ((List.range l).map fun j =>
    ((List.range j).filter fun i => !tbit mask i j l).length).sum).sum

/-- Over all groups there are 638,716 triples of positions with a clear bit. -/
theorem clear_total :
    ((List.range numGroups).map fun c =>
      clearCount (freeMasks.getD c 0) (groups.getD c []).length).sum = 638716 := by
  decide +kernel

end CON
