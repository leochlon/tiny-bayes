import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1313 : Cell := gridCell 64 14 16
theorem check1313 : PinnStaged.check cell1313 = true := by
  decide +kernel
theorem bound1313 {x y : ℝ} (h : cell1313.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1313 check1313 h
def cell1312 : Cell := gridCell 64 14 17
theorem check1312 : PinnStaged.check cell1312 = true := by
  decide +kernel
theorem bound1312 {x y : ℝ} (h : cell1312.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1312 check1312 h
def cell1311 : Cell := gridCell 64 15 16
theorem check1311 : PinnStaged.check cell1311 = true := by
  decide +kernel
theorem bound1311 {x y : ℝ} (h : cell1311.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1311 check1311 h
def cell1310 : Cell := gridCell 64 15 17
theorem check1310 : PinnStaged.check cell1310 = true := by
  decide +kernel
theorem bound1310 {x y : ℝ} (h : cell1310.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1310 check1310 h
def RawShard0106Cells : List Cell := [cell1313, cell1312, cell1311, cell1310]
theorem RawShard0106Valid : ValidCells RawShard0106Cells := by
  intro c hc x y h
  simp only [RawShard0106Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1313 | h1312 | h1311 | h1310
  · subst c
    exact bound1313 h
  · subst c
    exact bound1312 h
  · subst c
    exact bound1311 h
  · subst c
    exact bound1310 h
#print axioms RawShard0106Valid
end PinnCertFarm
