import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2791 : Cell := gridCell 64 24 10
theorem check2791 : PinnStaged.check cell2791 = true := by
  decide +kernel
theorem bound2791 {x y : ℝ} (h : cell2791.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2791 check2791 h
def cell2790 : Cell := gridCell 64 24 11
theorem check2790 : PinnStaged.check cell2790 = true := by
  decide +kernel
theorem bound2790 {x y : ℝ} (h : cell2790.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2790 check2790 h
def cell2789 : Cell := gridCell 64 25 10
theorem check2789 : PinnStaged.check cell2789 = true := by
  decide +kernel
theorem bound2789 {x y : ℝ} (h : cell2789.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2789 check2789 h
def cell2788 : Cell := gridCell 64 25 11
theorem check2788 : PinnStaged.check cell2788 = true := by
  decide +kernel
theorem bound2788 {x y : ℝ} (h : cell2788.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2788 check2788 h
def RawShard0177Cells : List Cell := [cell2791, cell2790, cell2789, cell2788]
theorem RawShard0177Valid : ValidCells RawShard0177Cells := by
  intro c hc x y h
  simp only [RawShard0177Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2791 | h2790 | h2789 | h2788
  · subst c
    exact bound2791 h
  · subst c
    exact bound2790 h
  · subst c
    exact bound2789 h
  · subst c
    exact bound2788 h
#print axioms RawShard0177Valid
end PinnCertFarm
