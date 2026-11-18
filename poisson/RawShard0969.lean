import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3871 : Cell := gridCell 64 35 0
theorem check3871 : PinnStaged.check cell3871 = true := by
  decide +kernel
theorem bound3871 {x y : ℝ} (h : cell3871.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3871 check3871 h
def cell3870 : Cell := gridCell 64 35 1
theorem check3870 : PinnStaged.check cell3870 = true := by
  decide +kernel
theorem bound3870 {x y : ℝ} (h : cell3870.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3870 check3870 h
def cell3869 : Cell := gridCell 64 34 2
theorem check3869 : PinnStaged.check cell3869 = true := by
  decide +kernel
theorem bound3869 {x y : ℝ} (h : cell3869.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3869 check3869 h
def cell3868 : Cell := gridCell 64 34 3
theorem check3868 : PinnStaged.check cell3868 = true := by
  decide +kernel
theorem bound3868 {x y : ℝ} (h : cell3868.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3868 check3868 h
def RawShard0969Cells : List Cell := [cell3871, cell3870, cell3869, cell3868]
theorem RawShard0969Valid : ValidCells RawShard0969Cells := by
  intro c hc x y h
  simp only [RawShard0969Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3871 | h3870 | h3869 | h3868
  · subst c
    exact bound3871 h
  · subst c
    exact bound3870 h
  · subst c
    exact bound3869 h
  · subst c
    exact bound3868 h
#print axioms RawShard0969Valid
end PinnCertFarm
