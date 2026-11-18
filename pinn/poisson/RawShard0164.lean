import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2779 : Cell := gridCell 64 24 4
theorem check2779 : PinnStaged.check cell2779 = true := by
  decide +kernel
theorem bound2779 {x y : ℝ} (h : cell2779.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2779 check2779 h
def cell2778 : Cell := gridCell 64 24 5
theorem check2778 : PinnStaged.check cell2778 = true := by
  decide +kernel
theorem bound2778 {x y : ℝ} (h : cell2778.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2778 check2778 h
def cell2777 : Cell := gridCell 64 25 4
theorem check2777 : PinnStaged.check cell2777 = true := by
  decide +kernel
theorem bound2777 {x y : ℝ} (h : cell2777.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2777 check2777 h
def cell2776 : Cell := gridCell 64 25 5
theorem check2776 : PinnStaged.check cell2776 = true := by
  decide +kernel
theorem bound2776 {x y : ℝ} (h : cell2776.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2776 check2776 h
def RawShard0164Cells : List Cell := [cell2779, cell2778, cell2777, cell2776]
theorem RawShard0164Valid : ValidCells RawShard0164Cells := by
  intro c hc x y h
  simp only [RawShard0164Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2779 | h2778 | h2777 | h2776
  · subst c
    exact bound2779 h
  · subst c
    exact bound2778 h
  · subst c
    exact bound2777 h
  · subst c
    exact bound2776 h
#print axioms RawShard0164Valid
end PinnCertFarm
