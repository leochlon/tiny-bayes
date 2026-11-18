import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6434 : Cell := gridCell 128 98 89
theorem check6434 : PinnStaged.check cell6434 = true := by
  decide +kernel
theorem bound6434 {x y : ℝ} (h : cell6434.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6434 check6434 h
def cell6433 : Cell := gridCell 128 99 88
theorem check6433 : PinnStaged.check cell6433 = true := by
  decide +kernel
theorem bound6433 {x y : ℝ} (h : cell6433.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6433 check6433 h
def cell6432 : Cell := gridCell 128 99 89
theorem check6432 : PinnStaged.check cell6432 = true := by
  decide +kernel
theorem bound6432 {x y : ℝ} (h : cell6432.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6432 check6432 h
def cell6431 : Cell := gridCell 128 98 90
theorem check6431 : PinnStaged.check cell6431 = true := by
  decide +kernel
theorem bound6431 {x y : ℝ} (h : cell6431.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6431 check6431 h
def RawShard1861Cells : List Cell := [cell6434, cell6433, cell6432, cell6431]
theorem RawShard1861Valid : ValidCells RawShard1861Cells := by
  intro c hc x y h
  simp only [RawShard1861Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6434 | h6433 | h6432 | h6431
  · subst c
    exact bound6434 h
  · subst c
    exact bound6433 h
  · subst c
    exact bound6432 h
  · subst c
    exact bound6431 h
#print axioms RawShard1861Valid
end PinnCertFarm
