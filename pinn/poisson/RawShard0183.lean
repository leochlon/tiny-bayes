import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2799 : Cell := gridCell 64 26 14
theorem check2799 : PinnStaged.check cell2799 = true := by
  decide +kernel
theorem bound2799 {x y : ℝ} (h : cell2799.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2799 check2799 h
def cell2798 : Cell := gridCell 64 26 15
theorem check2798 : PinnStaged.check cell2798 = true := by
  decide +kernel
theorem bound2798 {x y : ℝ} (h : cell2798.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2798 check2798 h
def cell2797 : Cell := gridCell 64 27 14
theorem check2797 : PinnStaged.check cell2797 = true := by
  decide +kernel
theorem bound2797 {x y : ℝ} (h : cell2797.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2797 check2797 h
def cell2796 : Cell := gridCell 64 27 15
theorem check2796 : PinnStaged.check cell2796 = true := by
  decide +kernel
theorem bound2796 {x y : ℝ} (h : cell2796.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2796 check2796 h
def RawShard0183Cells : List Cell := [cell2799, cell2798, cell2797, cell2796]
theorem RawShard0183Valid : ValidCells RawShard0183Cells := by
  intro c hc x y h
  simp only [RawShard0183Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2799 | h2798 | h2797 | h2796
  · subst c
    exact bound2799 h
  · subst c
    exact bound2798 h
  · subst c
    exact bound2797 h
  · subst c
    exact bound2796 h
#print axioms RawShard0183Valid
end PinnCertFarm
