import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell506 : Cell := gridCell 64 6 30
theorem check506 : PinnStaged.check cell506 = true := by
  decide +kernel
theorem bound506 {x y : ℝ} (h : cell506.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell506 check506 h
def cell505 : Cell := gridCell 64 6 31
theorem check505 : PinnStaged.check cell505 = true := by
  decide +kernel
theorem bound505 {x y : ℝ} (h : cell505.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell505 check505 h
def cell504 : Cell := gridCell 64 7 30
theorem check504 : PinnStaged.check cell504 = true := by
  decide +kernel
theorem bound504 {x y : ℝ} (h : cell504.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell504 check504 h
def cell503 : Cell := gridCell 64 7 31
theorem check503 : PinnStaged.check cell503 = true := by
  decide +kernel
theorem bound503 {x y : ℝ} (h : cell503.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell503 check503 h
def RawShard0095Cells : List Cell := [cell506, cell505, cell504, cell503]
theorem RawShard0095Valid : ValidCells RawShard0095Cells := by
  intro c hc x y h
  simp only [RawShard0095Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h506 | h505 | h504 | h503
  · subst c
    exact bound506 h
  · subst c
    exact bound505 h
  · subst c
    exact bound504 h
  · subst c
    exact bound503 h
#print axioms RawShard0095Valid
end PinnCertFarm
