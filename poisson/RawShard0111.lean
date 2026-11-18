import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1325 : Cell := gridCell 64 14 22
theorem check1325 : PinnStaged.check cell1325 = true := by
  decide +kernel
theorem bound1325 {x y : ℝ} (h : cell1325.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1325 check1325 h
def cell1324 : Cell := gridCell 64 14 23
theorem check1324 : PinnStaged.check cell1324 = true := by
  decide +kernel
theorem bound1324 {x y : ℝ} (h : cell1324.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1324 check1324 h
def cell1323 : Cell := gridCell 64 15 22
theorem check1323 : PinnStaged.check cell1323 = true := by
  decide +kernel
theorem bound1323 {x y : ℝ} (h : cell1323.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1323 check1323 h
def cell1322 : Cell := gridCell 64 15 23
theorem check1322 : PinnStaged.check cell1322 = true := by
  decide +kernel
theorem bound1322 {x y : ℝ} (h : cell1322.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1322 check1322 h
def RawShard0111Cells : List Cell := [cell1325, cell1324, cell1323, cell1322]
theorem RawShard0111Valid : ValidCells RawShard0111Cells := by
  intro c hc x y h
  simp only [RawShard0111Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1325 | h1324 | h1323 | h1322
  · subst c
    exact bound1325 h
  · subst c
    exact bound1324 h
  · subst c
    exact bound1323 h
  · subst c
    exact bound1322 h
#print axioms RawShard0111Valid
end PinnCertFarm
