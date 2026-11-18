import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4638 : Cell := gridCell 128 75 80
theorem check4638 : PinnStaged.check cell4638 = true := by
  decide +kernel
theorem bound4638 {x y : ℝ} (h : cell4638.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4638 check4638 h
def cell4637 : Cell := gridCell 128 75 81
theorem check4637 : PinnStaged.check cell4637 = true := by
  decide +kernel
theorem bound4637 {x y : ℝ} (h : cell4637.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4637 check4637 h
def cell4636 : Cell := gridCell 128 74 82
theorem check4636 : PinnStaged.check cell4636 = true := by
  decide +kernel
theorem bound4636 {x y : ℝ} (h : cell4636.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4636 check4636 h
def cell4635 : Cell := gridCell 128 74 83
theorem check4635 : PinnStaged.check cell4635 = true := by
  decide +kernel
theorem bound4635 {x y : ℝ} (h : cell4635.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4635 check4635 h
def RawShard1411Cells : List Cell := [cell4638, cell4637, cell4636, cell4635]
theorem RawShard1411Valid : ValidCells RawShard1411Cells := by
  intro c hc x y h
  simp only [RawShard1411Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4638 | h4637 | h4636 | h4635
  · subst c
    exact bound4638 h
  · subst c
    exact bound4637 h
  · subst c
    exact bound4636 h
  · subst c
    exact bound4635 h
#print axioms RawShard1411Valid
end PinnCertFarm
