import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4606 : Cell := gridCell 128 79 80
theorem check4606 : PinnStaged.check cell4606 = true := by
  decide +kernel
theorem bound4606 {x y : ℝ} (h : cell4606.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4606 check4606 h
def cell4605 : Cell := gridCell 128 79 81
theorem check4605 : PinnStaged.check cell4605 = true := by
  decide +kernel
theorem bound4605 {x y : ℝ} (h : cell4605.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4605 check4605 h
def cell4604 : Cell := gridCell 128 78 82
theorem check4604 : PinnStaged.check cell4604 = true := by
  decide +kernel
theorem bound4604 {x y : ℝ} (h : cell4604.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4604 check4604 h
def cell4603 : Cell := gridCell 128 78 83
theorem check4603 : PinnStaged.check cell4603 = true := by
  decide +kernel
theorem bound4603 {x y : ℝ} (h : cell4603.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4603 check4603 h
def RawShard1419Cells : List Cell := [cell4606, cell4605, cell4604, cell4603]
theorem RawShard1419Valid : ValidCells RawShard1419Cells := by
  intro c hc x y h
  simp only [RawShard1419Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4606 | h4605 | h4604 | h4603
  · subst c
    exact bound4606 h
  · subst c
    exact bound4605 h
  · subst c
    exact bound4604 h
  · subst c
    exact bound4603 h
#print axioms RawShard1419Valid
end PinnCertFarm
