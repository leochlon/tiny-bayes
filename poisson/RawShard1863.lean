import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6426 : Cell := gridCell 128 96 93
theorem check6426 : PinnStaged.check cell6426 = true := by
  decide +kernel
theorem bound6426 {x y : ℝ} (h : cell6426.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6426 check6426 h
def cell6425 : Cell := gridCell 128 97 92
theorem check6425 : PinnStaged.check cell6425 = true := by
  decide +kernel
theorem bound6425 {x y : ℝ} (h : cell6425.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6425 check6425 h
def cell6424 : Cell := gridCell 128 97 93
theorem check6424 : PinnStaged.check cell6424 = true := by
  decide +kernel
theorem bound6424 {x y : ℝ} (h : cell6424.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6424 check6424 h
def cell6423 : Cell := gridCell 128 96 94
theorem check6423 : PinnStaged.check cell6423 = true := by
  decide +kernel
theorem bound6423 {x y : ℝ} (h : cell6423.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6423 check6423 h
def RawShard1863Cells : List Cell := [cell6426, cell6425, cell6424, cell6423]
theorem RawShard1863Valid : ValidCells RawShard1863Cells := by
  intro c hc x y h
  simp only [RawShard1863Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6426 | h6425 | h6424 | h6423
  · subst c
    exact bound6426 h
  · subst c
    exact bound6425 h
  · subst c
    exact bound6424 h
  · subst c
    exact bound6423 h
#print axioms RawShard1863Valid
end PinnCertFarm
