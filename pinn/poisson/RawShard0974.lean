import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3883 : Cell := gridCell 64 35 6
theorem check3883 : PinnStaged.check cell3883 = true := by
  decide +kernel
theorem bound3883 {x y : ℝ} (h : cell3883.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3883 check3883 h
def cell3882 : Cell := gridCell 64 35 7
theorem check3882 : PinnStaged.check cell3882 = true := by
  decide +kernel
theorem bound3882 {x y : ℝ} (h : cell3882.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3882 check3882 h
def cell4440 : Cell := gridCell 64 36 0
theorem check4440 : PinnStaged.check cell4440 = true := by
  decide +kernel
theorem bound4440 {x y : ℝ} (h : cell4440.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4440 check4440 h
def cell4439 : Cell := gridCell 64 36 1
theorem check4439 : PinnStaged.check cell4439 = true := by
  decide +kernel
theorem bound4439 {x y : ℝ} (h : cell4439.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4439 check4439 h
def RawShard0974Cells : List Cell := [cell3883, cell3882, cell4440, cell4439]
theorem RawShard0974Valid : ValidCells RawShard0974Cells := by
  intro c hc x y h
  simp only [RawShard0974Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3883 | h3882 | h4440 | h4439
  · subst c
    exact bound3883 h
  · subst c
    exact bound3882 h
  · subst c
    exact bound4440 h
  · subst c
    exact bound4439 h
#print axioms RawShard0974Valid
end PinnCertFarm
