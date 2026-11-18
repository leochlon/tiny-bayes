import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell478 : Cell := gridCell 64 6 20
theorem check478 : PinnStaged.check cell478 = true := by
  decide +kernel
theorem bound478 {x y : ℝ} (h : cell478.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell478 check478 h
def cell477 : Cell := gridCell 64 6 21
theorem check477 : PinnStaged.check cell477 = true := by
  decide +kernel
theorem bound477 {x y : ℝ} (h : cell477.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell477 check477 h
def cell476 : Cell := gridCell 64 7 20
theorem check476 : PinnStaged.check cell476 = true := by
  decide +kernel
theorem bound476 {x y : ℝ} (h : cell476.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell476 check476 h
def cell475 : Cell := gridCell 64 7 21
theorem check475 : PinnStaged.check cell475 = true := by
  decide +kernel
theorem bound475 {x y : ℝ} (h : cell475.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell475 check475 h
def RawShard0078Cells : List Cell := [cell478, cell477, cell476, cell475]
theorem RawShard0078Valid : ValidCells RawShard0078Cells := by
  intro c hc x y h
  simp only [RawShard0078Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h478 | h477 | h476 | h475
  · subst c
    exact bound478 h
  · subst c
    exact bound477 h
  · subst c
    exact bound476 h
  · subst c
    exact bound475 h
#print axioms RawShard0078Valid
end PinnCertFarm
