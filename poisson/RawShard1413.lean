import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4630 : Cell := gridCell 128 73 84
theorem check4630 : PinnStaged.check cell4630 = true := by
  decide +kernel
theorem bound4630 {x y : ℝ} (h : cell4630.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4630 check4630 h
def cell4629 : Cell := gridCell 128 73 85
theorem check4629 : PinnStaged.check cell4629 = true := by
  decide +kernel
theorem bound4629 {x y : ℝ} (h : cell4629.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4629 check4629 h
def cell4628 : Cell := gridCell 128 72 86
theorem check4628 : PinnStaged.check cell4628 = true := by
  decide +kernel
theorem bound4628 {x y : ℝ} (h : cell4628.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4628 check4628 h
def cell4627 : Cell := gridCell 128 72 87
theorem check4627 : PinnStaged.check cell4627 = true := by
  decide +kernel
theorem bound4627 {x y : ℝ} (h : cell4627.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4627 check4627 h
def RawShard1413Cells : List Cell := [cell4630, cell4629, cell4628, cell4627]
theorem RawShard1413Valid : ValidCells RawShard1413Cells := by
  intro c hc x y h
  simp only [RawShard1413Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4630 | h4629 | h4628 | h4627
  · subst c
    exact bound4630 h
  · subst c
    exact bound4629 h
  · subst c
    exact bound4628 h
  · subst c
    exact bound4627 h
#print axioms RawShard1413Valid
end PinnCertFarm
