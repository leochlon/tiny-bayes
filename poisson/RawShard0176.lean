import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2795 : Cell := gridCell 64 24 8
theorem check2795 : PinnStaged.check cell2795 = true := by
  decide +kernel
theorem bound2795 {x y : ℝ} (h : cell2795.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2795 check2795 h
def cell2794 : Cell := gridCell 64 24 9
theorem check2794 : PinnStaged.check cell2794 = true := by
  decide +kernel
theorem bound2794 {x y : ℝ} (h : cell2794.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2794 check2794 h
def cell2793 : Cell := gridCell 64 25 8
theorem check2793 : PinnStaged.check cell2793 = true := by
  decide +kernel
theorem bound2793 {x y : ℝ} (h : cell2793.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2793 check2793 h
def cell2792 : Cell := gridCell 64 25 9
theorem check2792 : PinnStaged.check cell2792 = true := by
  decide +kernel
theorem bound2792 {x y : ℝ} (h : cell2792.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2792 check2792 h
def RawShard0176Cells : List Cell := [cell2795, cell2794, cell2793, cell2792]
theorem RawShard0176Valid : ValidCells RawShard0176Cells := by
  intro c hc x y h
  simp only [RawShard0176Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2795 | h2794 | h2793 | h2792
  · subst c
    exact bound2795 h
  · subst c
    exact bound2794 h
  · subst c
    exact bound2793 h
  · subst c
    exact bound2792 h
#print axioms RawShard0176Valid
end PinnCertFarm
