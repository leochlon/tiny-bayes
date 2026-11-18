import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1357 : Cell := gridCell 64 14 30
theorem check1357 : PinnStaged.check cell1357 = true := by
  decide +kernel
theorem bound1357 {x y : ℝ} (h : cell1357.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1357 check1357 h
def cell1356 : Cell := gridCell 64 14 31
theorem check1356 : PinnStaged.check cell1356 = true := by
  decide +kernel
theorem bound1356 {x y : ℝ} (h : cell1356.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1356 check1356 h
def cell1355 : Cell := gridCell 64 15 30
theorem check1355 : PinnStaged.check cell1355 = true := by
  decide +kernel
theorem bound1355 {x y : ℝ} (h : cell1355.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1355 check1355 h
def cell1354 : Cell := gridCell 64 15 31
theorem check1354 : PinnStaged.check cell1354 = true := by
  decide +kernel
theorem bound1354 {x y : ℝ} (h : cell1354.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1354 check1354 h
def RawShard0127Cells : List Cell := [cell1357, cell1356, cell1355, cell1354]
theorem RawShard0127Valid : ValidCells RawShard0127Cells := by
  intro c hc x y h
  simp only [RawShard0127Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1357 | h1356 | h1355 | h1354
  · subst c
    exact bound1357 h
  · subst c
    exact bound1356 h
  · subst c
    exact bound1355 h
  · subst c
    exact bound1354 h
#print axioms RawShard0127Valid
end PinnCertFarm
