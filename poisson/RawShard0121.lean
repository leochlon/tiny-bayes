import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1349 : Cell := gridCell 64 12 26
theorem check1349 : PinnStaged.check cell1349 = true := by
  decide +kernel
theorem bound1349 {x y : ℝ} (h : cell1349.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1349 check1349 h
def cell1348 : Cell := gridCell 64 12 27
theorem check1348 : PinnStaged.check cell1348 = true := by
  decide +kernel
theorem bound1348 {x y : ℝ} (h : cell1348.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1348 check1348 h
def cell1347 : Cell := gridCell 64 13 26
theorem check1347 : PinnStaged.check cell1347 = true := by
  decide +kernel
theorem bound1347 {x y : ℝ} (h : cell1347.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1347 check1347 h
def cell1346 : Cell := gridCell 64 13 27
theorem check1346 : PinnStaged.check cell1346 = true := by
  decide +kernel
theorem bound1346 {x y : ℝ} (h : cell1346.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1346 check1346 h
def RawShard0121Cells : List Cell := [cell1349, cell1348, cell1347, cell1346]
theorem RawShard0121Valid : ValidCells RawShard0121Cells := by
  intro c hc x y h
  simp only [RawShard0121Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1349 | h1348 | h1347 | h1346
  · subst c
    exact bound1349 h
  · subst c
    exact bound1348 h
  · subst c
    exact bound1347 h
  · subst c
    exact bound1346 h
#print axioms RawShard0121Valid
end PinnCertFarm
