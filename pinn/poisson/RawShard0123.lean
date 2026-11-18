import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1341 : Cell := gridCell 64 14 26
theorem check1341 : PinnStaged.check cell1341 = true := by
  decide +kernel
theorem bound1341 {x y : ℝ} (h : cell1341.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1341 check1341 h
def cell1340 : Cell := gridCell 64 14 27
theorem check1340 : PinnStaged.check cell1340 = true := by
  decide +kernel
theorem bound1340 {x y : ℝ} (h : cell1340.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1340 check1340 h
def cell1339 : Cell := gridCell 64 15 26
theorem check1339 : PinnStaged.check cell1339 = true := by
  decide +kernel
theorem bound1339 {x y : ℝ} (h : cell1339.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1339 check1339 h
def cell1338 : Cell := gridCell 64 15 27
theorem check1338 : PinnStaged.check cell1338 = true := by
  decide +kernel
theorem bound1338 {x y : ℝ} (h : cell1338.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1338 check1338 h
def RawShard0123Cells : List Cell := [cell1341, cell1340, cell1339, cell1338]
theorem RawShard0123Valid : ValidCells RawShard0123Cells := by
  intro c hc x y h
  simp only [RawShard0123Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1341 | h1340 | h1339 | h1338
  · subst c
    exact bound1341 h
  · subst c
    exact bound1340 h
  · subst c
    exact bound1339 h
  · subst c
    exact bound1338 h
#print axioms RawShard0123Valid
end PinnCertFarm
