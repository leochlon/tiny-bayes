import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2783 : Cell := gridCell 64 26 10
theorem check2783 : PinnStaged.check cell2783 = true := by
  decide +kernel
theorem bound2783 {x y : ℝ} (h : cell2783.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2783 check2783 h
def cell2782 : Cell := gridCell 64 26 11
theorem check2782 : PinnStaged.check cell2782 = true := by
  decide +kernel
theorem bound2782 {x y : ℝ} (h : cell2782.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2782 check2782 h
def cell2781 : Cell := gridCell 64 27 10
theorem check2781 : PinnStaged.check cell2781 = true := by
  decide +kernel
theorem bound2781 {x y : ℝ} (h : cell2781.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2781 check2781 h
def cell2780 : Cell := gridCell 64 27 11
theorem check2780 : PinnStaged.check cell2780 = true := by
  decide +kernel
theorem bound2780 {x y : ℝ} (h : cell2780.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2780 check2780 h
def RawShard0179Cells : List Cell := [cell2783, cell2782, cell2781, cell2780]
theorem RawShard0179Valid : ValidCells RawShard0179Cells := by
  intro c hc x y h
  simp only [RawShard0179Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2783 | h2782 | h2781 | h2780
  · subst c
    exact bound2783 h
  · subst c
    exact bound2782 h
  · subst c
    exact bound2781 h
  · subst c
    exact bound2780 h
#print axioms RawShard0179Valid
end PinnCertFarm
