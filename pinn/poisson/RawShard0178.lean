import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2787 : Cell := gridCell 64 26 8
theorem check2787 : PinnStaged.check cell2787 = true := by
  decide +kernel
theorem bound2787 {x y : ℝ} (h : cell2787.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2787 check2787 h
def cell2786 : Cell := gridCell 64 26 9
theorem check2786 : PinnStaged.check cell2786 = true := by
  decide +kernel
theorem bound2786 {x y : ℝ} (h : cell2786.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2786 check2786 h
def cell2785 : Cell := gridCell 64 27 8
theorem check2785 : PinnStaged.check cell2785 = true := by
  decide +kernel
theorem bound2785 {x y : ℝ} (h : cell2785.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2785 check2785 h
def cell2784 : Cell := gridCell 64 27 9
theorem check2784 : PinnStaged.check cell2784 = true := by
  decide +kernel
theorem bound2784 {x y : ℝ} (h : cell2784.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2784 check2784 h
def RawShard0178Cells : List Cell := [cell2787, cell2786, cell2785, cell2784]
theorem RawShard0178Valid : ValidCells RawShard0178Cells := by
  intro c hc x y h
  simp only [RawShard0178Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2787 | h2786 | h2785 | h2784
  · subst c
    exact bound2787 h
  · subst c
    exact bound2786 h
  · subst c
    exact bound2785 h
  · subst c
    exact bound2784 h
#print axioms RawShard0178Valid
end PinnCertFarm
