import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell111 : Cell := gridCell 64 0 24
theorem check111 : PinnStaged.check cell111 = true := by
  decide +kernel
theorem bound111 {x y : ℝ} (h : cell111.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell111 check111 h
def cell110 : Cell := gridCell 64 0 25
theorem check110 : PinnStaged.check cell110 = true := by
  decide +kernel
theorem bound110 {x y : ℝ} (h : cell110.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell110 check110 h
def cell109 : Cell := gridCell 64 1 24
theorem check109 : PinnStaged.check cell109 = true := by
  decide +kernel
theorem bound109 {x y : ℝ} (h : cell109.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell109 check109 h
def cell108 : Cell := gridCell 64 1 25
theorem check108 : PinnStaged.check cell108 = true := by
  decide +kernel
theorem bound108 {x y : ℝ} (h : cell108.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell108 check108 h
def RawShard0080Cells : List Cell := [cell111, cell110, cell109, cell108]
theorem RawShard0080Valid : ValidCells RawShard0080Cells := by
  intro c hc x y h
  simp only [RawShard0080Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h111 | h110 | h109 | h108
  · subst c
    exact bound111 h
  · subst c
    exact bound110 h
  · subst c
    exact bound109 h
  · subst c
    exact bound108 h
#print axioms RawShard0080Valid
end PinnCertFarm
