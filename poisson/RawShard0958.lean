import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3811 : Cell := gridCell 128 63 120
theorem check3811 : PinnStaged.check cell3811 = true := by
  decide +kernel
theorem bound3811 {x y : ℝ} (h : cell3811.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3811 check3811 h
def cell3810 : Cell := gridCell 128 63 121
theorem check3810 : PinnStaged.check cell3810 = true := by
  decide +kernel
theorem bound3810 {x y : ℝ} (h : cell3810.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3810 check3810 h
def cell3809 : Cell := gridCell 128 62 122
theorem check3809 : PinnStaged.check cell3809 = true := by
  decide +kernel
theorem bound3809 {x y : ℝ} (h : cell3809.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3809 check3809 h
def cell3808 : Cell := gridCell 128 62 123
theorem check3808 : PinnStaged.check cell3808 = true := by
  decide +kernel
theorem bound3808 {x y : ℝ} (h : cell3808.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3808 check3808 h
def RawShard0958Cells : List Cell := [cell3811, cell3810, cell3809, cell3808]
theorem RawShard0958Valid : ValidCells RawShard0958Cells := by
  intro c hc x y h
  simp only [RawShard0958Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3811 | h3810 | h3809 | h3808
  · subst c
    exact bound3811 h
  · subst c
    exact bound3810 h
  · subst c
    exact bound3809 h
  · subst c
    exact bound3808 h
#print axioms RawShard0958Valid
end PinnCertFarm
