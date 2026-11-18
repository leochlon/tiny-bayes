import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2775 : Cell := gridCell 64 24 6
theorem check2775 : PinnStaged.check cell2775 = true := by
  decide +kernel
theorem bound2775 {x y : ℝ} (h : cell2775.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2775 check2775 h
def cell2774 : Cell := gridCell 64 24 7
theorem check2774 : PinnStaged.check cell2774 = true := by
  decide +kernel
theorem bound2774 {x y : ℝ} (h : cell2774.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2774 check2774 h
def cell2773 : Cell := gridCell 64 25 6
theorem check2773 : PinnStaged.check cell2773 = true := by
  decide +kernel
theorem bound2773 {x y : ℝ} (h : cell2773.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2773 check2773 h
def cell2772 : Cell := gridCell 64 25 7
theorem check2772 : PinnStaged.check cell2772 = true := by
  decide +kernel
theorem bound2772 {x y : ℝ} (h : cell2772.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2772 check2772 h
def RawShard0165Cells : List Cell := [cell2775, cell2774, cell2773, cell2772]
theorem RawShard0165Valid : ValidCells RawShard0165Cells := by
  intro c hc x y h
  simp only [RawShard0165Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2775 | h2774 | h2773 | h2772
  · subst c
    exact bound2775 h
  · subst c
    exact bound2774 h
  · subst c
    exact bound2773 h
  · subst c
    exact bound2772 h
#print axioms RawShard0165Valid
end PinnCertFarm
