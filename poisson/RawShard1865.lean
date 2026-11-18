import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6418 : Cell := gridCell 128 98 93
theorem check6418 : PinnStaged.check cell6418 = true := by
  decide +kernel
theorem bound6418 {x y : ℝ} (h : cell6418.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6418 check6418 h
def cell6417 : Cell := gridCell 128 99 92
theorem check6417 : PinnStaged.check cell6417 = true := by
  decide +kernel
theorem bound6417 {x y : ℝ} (h : cell6417.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6417 check6417 h
def cell6416 : Cell := gridCell 128 99 93
theorem check6416 : PinnStaged.check cell6416 = true := by
  decide +kernel
theorem bound6416 {x y : ℝ} (h : cell6416.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6416 check6416 h
def cell6415 : Cell := gridCell 128 98 94
theorem check6415 : PinnStaged.check cell6415 = true := by
  decide +kernel
theorem bound6415 {x y : ℝ} (h : cell6415.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6415 check6415 h
def RawShard1865Cells : List Cell := [cell6418, cell6417, cell6416, cell6415]
theorem RawShard1865Valid : ValidCells RawShard1865Cells := by
  intro c hc x y h
  simp only [RawShard1865Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6418 | h6417 | h6416 | h6415
  · subst c
    exact bound6418 h
  · subst c
    exact bound6417 h
  · subst c
    exact bound6416 h
  · subst c
    exact bound6415 h
#print axioms RawShard1865Valid
end PinnCertFarm
