import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4438 : Cell := gridCell 64 37 0
theorem check4438 : PinnStaged.check cell4438 = true := by
  decide +kernel
theorem bound4438 {x y : ℝ} (h : cell4438.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4438 check4438 h
def cell4437 : Cell := gridCell 64 37 1
theorem check4437 : PinnStaged.check cell4437 = true := by
  decide +kernel
theorem bound4437 {x y : ℝ} (h : cell4437.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4437 check4437 h
def cell4436 : Cell := gridCell 64 36 2
theorem check4436 : PinnStaged.check cell4436 = true := by
  decide +kernel
theorem bound4436 {x y : ℝ} (h : cell4436.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4436 check4436 h
def cell4435 : Cell := gridCell 64 36 3
theorem check4435 : PinnStaged.check cell4435 = true := by
  decide +kernel
theorem bound4435 {x y : ℝ} (h : cell4435.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4435 check4435 h
def RawShard0975Cells : List Cell := [cell4438, cell4437, cell4436, cell4435]
theorem RawShard0975Valid : ValidCells RawShard0975Cells := by
  intro c hc x y h
  simp only [RawShard0975Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4438 | h4437 | h4436 | h4435
  · subst c
    exact bound4438 h
  · subst c
    exact bound4437 h
  · subst c
    exact bound4436 h
  · subst c
    exact bound4435 h
#print axioms RawShard0975Valid
end PinnCertFarm
