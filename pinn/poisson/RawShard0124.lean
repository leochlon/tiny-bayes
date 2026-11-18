import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1369 : Cell := gridCell 64 12 28
theorem check1369 : PinnStaged.check cell1369 = true := by
  decide +kernel
theorem bound1369 {x y : ℝ} (h : cell1369.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1369 check1369 h
def cell1368 : Cell := gridCell 64 12 29
theorem check1368 : PinnStaged.check cell1368 = true := by
  decide +kernel
theorem bound1368 {x y : ℝ} (h : cell1368.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1368 check1368 h
def cell1367 : Cell := gridCell 64 13 28
theorem check1367 : PinnStaged.check cell1367 = true := by
  decide +kernel
theorem bound1367 {x y : ℝ} (h : cell1367.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1367 check1367 h
def cell1366 : Cell := gridCell 64 13 29
theorem check1366 : PinnStaged.check cell1366 = true := by
  decide +kernel
theorem bound1366 {x y : ℝ} (h : cell1366.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1366 check1366 h
def RawShard0124Cells : List Cell := [cell1369, cell1368, cell1367, cell1366]
theorem RawShard0124Valid : ValidCells RawShard0124Cells := by
  intro c hc x y h
  simp only [RawShard0124Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1369 | h1368 | h1367 | h1366
  · subst c
    exact bound1369 h
  · subst c
    exact bound1368 h
  · subst c
    exact bound1367 h
  · subst c
    exact bound1366 h
#print axioms RawShard0124Valid
end PinnCertFarm
