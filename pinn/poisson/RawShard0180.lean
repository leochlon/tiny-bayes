import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2811 : Cell := gridCell 64 24 12
theorem check2811 : PinnStaged.check cell2811 = true := by
  decide +kernel
theorem bound2811 {x y : ℝ} (h : cell2811.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2811 check2811 h
def cell2810 : Cell := gridCell 64 24 13
theorem check2810 : PinnStaged.check cell2810 = true := by
  decide +kernel
theorem bound2810 {x y : ℝ} (h : cell2810.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2810 check2810 h
def cell2809 : Cell := gridCell 64 25 12
theorem check2809 : PinnStaged.check cell2809 = true := by
  decide +kernel
theorem bound2809 {x y : ℝ} (h : cell2809.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2809 check2809 h
def cell2808 : Cell := gridCell 64 25 13
theorem check2808 : PinnStaged.check cell2808 = true := by
  decide +kernel
theorem bound2808 {x y : ℝ} (h : cell2808.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2808 check2808 h
def RawShard0180Cells : List Cell := [cell2811, cell2810, cell2809, cell2808]
theorem RawShard0180Valid : ValidCells RawShard0180Cells := by
  intro c hc x y h
  simp only [RawShard0180Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2811 | h2810 | h2809 | h2808
  · subst c
    exact bound2811 h
  · subst c
    exact bound2810 h
  · subst c
    exact bound2809 h
  · subst c
    exact bound2808 h
#print axioms RawShard0180Valid
end PinnCertFarm
