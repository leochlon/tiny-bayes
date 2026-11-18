import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6442 : Cell := gridCell 128 96 89
theorem check6442 : PinnStaged.check cell6442 = true := by
  decide +kernel
theorem bound6442 {x y : ℝ} (h : cell6442.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6442 check6442 h
def cell6441 : Cell := gridCell 128 97 88
theorem check6441 : PinnStaged.check cell6441 = true := by
  decide +kernel
theorem bound6441 {x y : ℝ} (h : cell6441.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6441 check6441 h
def cell6440 : Cell := gridCell 128 97 89
theorem check6440 : PinnStaged.check cell6440 = true := by
  decide +kernel
theorem bound6440 {x y : ℝ} (h : cell6440.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6440 check6440 h
def cell6439 : Cell := gridCell 128 96 90
theorem check6439 : PinnStaged.check cell6439 = true := by
  decide +kernel
theorem bound6439 {x y : ℝ} (h : cell6439.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6439 check6439 h
def RawShard1859Cells : List Cell := [cell6442, cell6441, cell6440, cell6439]
theorem RawShard1859Valid : ValidCells RawShard1859Cells := by
  intro c hc x y h
  simp only [RawShard1859Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6442 | h6441 | h6440 | h6439
  · subst c
    exact bound6442 h
  · subst c
    exact bound6441 h
  · subst c
    exact bound6440 h
  · subst c
    exact bound6439 h
#print axioms RawShard1859Valid
end PinnCertFarm
