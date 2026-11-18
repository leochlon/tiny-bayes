import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell474 : Cell := gridCell 64 6 22
theorem check474 : PinnStaged.check cell474 = true := by
  decide +kernel
theorem bound474 {x y : ℝ} (h : cell474.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell474 check474 h
def cell473 : Cell := gridCell 64 6 23
theorem check473 : PinnStaged.check cell473 = true := by
  decide +kernel
theorem bound473 {x y : ℝ} (h : cell473.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell473 check473 h
def cell472 : Cell := gridCell 64 7 22
theorem check472 : PinnStaged.check cell472 = true := by
  decide +kernel
theorem bound472 {x y : ℝ} (h : cell472.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell472 check472 h
def cell471 : Cell := gridCell 64 7 23
theorem check471 : PinnStaged.check cell471 = true := by
  decide +kernel
theorem bound471 {x y : ℝ} (h : cell471.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell471 check471 h
def RawShard0079Cells : List Cell := [cell474, cell473, cell472, cell471]
theorem RawShard0079Valid : ValidCells RawShard0079Cells := by
  intro c hc x y h
  simp only [RawShard0079Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h474 | h473 | h472 | h471
  · subst c
    exact bound474 h
  · subst c
    exact bound473 h
  · subst c
    exact bound472 h
  · subst c
    exact bound471 h
#print axioms RawShard0079Valid
end PinnCertFarm
