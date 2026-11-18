import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2807 : Cell := gridCell 64 24 14
theorem check2807 : PinnStaged.check cell2807 = true := by
  decide +kernel
theorem bound2807 {x y : ℝ} (h : cell2807.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2807 check2807 h
def cell2806 : Cell := gridCell 64 24 15
theorem check2806 : PinnStaged.check cell2806 = true := by
  decide +kernel
theorem bound2806 {x y : ℝ} (h : cell2806.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2806 check2806 h
def cell2805 : Cell := gridCell 64 25 14
theorem check2805 : PinnStaged.check cell2805 = true := by
  decide +kernel
theorem bound2805 {x y : ℝ} (h : cell2805.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2805 check2805 h
def cell2804 : Cell := gridCell 64 25 15
theorem check2804 : PinnStaged.check cell2804 = true := by
  decide +kernel
theorem bound2804 {x y : ℝ} (h : cell2804.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2804 check2804 h
def RawShard0181Cells : List Cell := [cell2807, cell2806, cell2805, cell2804]
theorem RawShard0181Valid : ValidCells RawShard0181Cells := by
  intro c hc x y h
  simp only [RawShard0181Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2807 | h2806 | h2805 | h2804
  · subst c
    exact bound2807 h
  · subst c
    exact bound2806 h
  · subst c
    exact bound2805 h
  · subst c
    exact bound2804 h
#print axioms RawShard0181Valid
end PinnCertFarm
