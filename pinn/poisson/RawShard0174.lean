import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3336 : Cell := gridCell 64 30 4
theorem check3336 : PinnStaged.check cell3336 = true := by
  decide +kernel
theorem bound3336 {x y : ℝ} (h : cell3336.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3336 check3336 h
def cell3335 : Cell := gridCell 64 30 5
theorem check3335 : PinnStaged.check cell3335 = true := by
  decide +kernel
theorem bound3335 {x y : ℝ} (h : cell3335.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3335 check3335 h
def cell3334 : Cell := gridCell 64 31 4
theorem check3334 : PinnStaged.check cell3334 = true := by
  decide +kernel
theorem bound3334 {x y : ℝ} (h : cell3334.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3334 check3334 h
def cell3333 : Cell := gridCell 64 31 5
theorem check3333 : PinnStaged.check cell3333 = true := by
  decide +kernel
theorem bound3333 {x y : ℝ} (h : cell3333.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3333 check3333 h
def RawShard0174Cells : List Cell := [cell3336, cell3335, cell3334, cell3333]
theorem RawShard0174Valid : ValidCells RawShard0174Cells := by
  intro c hc x y h
  simp only [RawShard0174Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3336 | h3335 | h3334 | h3333
  · subst c
    exact bound3336 h
  · subst c
    exact bound3335 h
  · subst c
    exact bound3334 h
  · subst c
    exact bound3333 h
#print axioms RawShard0174Valid
end PinnCertFarm
