import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2803 : Cell := gridCell 64 26 12
theorem check2803 : PinnStaged.check cell2803 = true := by
  decide +kernel
theorem bound2803 {x y : ℝ} (h : cell2803.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2803 check2803 h
def cell2802 : Cell := gridCell 64 26 13
theorem check2802 : PinnStaged.check cell2802 = true := by
  decide +kernel
theorem bound2802 {x y : ℝ} (h : cell2802.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2802 check2802 h
def cell2801 : Cell := gridCell 64 27 12
theorem check2801 : PinnStaged.check cell2801 = true := by
  decide +kernel
theorem bound2801 {x y : ℝ} (h : cell2801.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2801 check2801 h
def cell2800 : Cell := gridCell 64 27 13
theorem check2800 : PinnStaged.check cell2800 = true := by
  decide +kernel
theorem bound2800 {x y : ℝ} (h : cell2800.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2800 check2800 h
def RawShard0182Cells : List Cell := [cell2803, cell2802, cell2801, cell2800]
theorem RawShard0182Valid : ValidCells RawShard0182Cells := by
  intro c hc x y h
  simp only [RawShard0182Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2803 | h2802 | h2801 | h2800
  · subst c
    exact bound2803 h
  · subst c
    exact bound2802 h
  · subst c
    exact bound2801 h
  · subst c
    exact bound2800 h
#print axioms RawShard0182Valid
end PinnCertFarm
