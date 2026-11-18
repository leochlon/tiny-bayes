import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3875 : Cell := gridCell 64 33 2
theorem check3875 : PinnStaged.check cell3875 = true := by
  decide +kernel
theorem bound3875 {x y : ℝ} (h : cell3875.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3875 check3875 h
def cell3874 : Cell := gridCell 64 33 3
theorem check3874 : PinnStaged.check cell3874 = true := by
  decide +kernel
theorem bound3874 {x y : ℝ} (h : cell3874.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3874 check3874 h
def cell3873 : Cell := gridCell 64 34 0
theorem check3873 : PinnStaged.check cell3873 = true := by
  decide +kernel
theorem bound3873 {x y : ℝ} (h : cell3873.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3873 check3873 h
def cell3872 : Cell := gridCell 64 34 1
theorem check3872 : PinnStaged.check cell3872 = true := by
  decide +kernel
theorem bound3872 {x y : ℝ} (h : cell3872.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3872 check3872 h
def RawShard0968Cells : List Cell := [cell3875, cell3874, cell3873, cell3872]
theorem RawShard0968Valid : ValidCells RawShard0968Cells := by
  intro c hc x y h
  simp only [RawShard0968Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3875 | h3874 | h3873 | h3872
  · subst c
    exact bound3875 h
  · subst c
    exact bound3874 h
  · subst c
    exact bound3873 h
  · subst c
    exact bound3872 h
#print axioms RawShard0968Valid
end PinnCertFarm
