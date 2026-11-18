import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4626 : Cell := gridCell 128 73 86
theorem check4626 : PinnStaged.check cell4626 = true := by
  decide +kernel
theorem bound4626 {x y : ℝ} (h : cell4626.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4626 check4626 h
def cell4625 : Cell := gridCell 128 73 87
theorem check4625 : PinnStaged.check cell4625 = true := by
  decide +kernel
theorem bound4625 {x y : ℝ} (h : cell4625.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4625 check4625 h
def cell4624 : Cell := gridCell 128 74 84
theorem check4624 : PinnStaged.check cell4624 = true := by
  decide +kernel
theorem bound4624 {x y : ℝ} (h : cell4624.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4624 check4624 h
def cell4623 : Cell := gridCell 128 74 85
theorem check4623 : PinnStaged.check cell4623 = true := by
  decide +kernel
theorem bound4623 {x y : ℝ} (h : cell4623.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4623 check4623 h
def RawShard1414Cells : List Cell := [cell4626, cell4625, cell4624, cell4623]
theorem RawShard1414Valid : ValidCells RawShard1414Cells := by
  intro c hc x y h
  simp only [RawShard1414Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4626 | h4625 | h4624 | h4623
  · subst c
    exact bound4626 h
  · subst c
    exact bound4625 h
  · subst c
    exact bound4624 h
  · subst c
    exact bound4623 h
#print axioms RawShard1414Valid
end PinnCertFarm
