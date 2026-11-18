import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2767 : Cell := gridCell 64 26 6
theorem check2767 : PinnStaged.check cell2767 = true := by
  decide +kernel
theorem bound2767 {x y : ℝ} (h : cell2767.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2767 check2767 h
def cell2766 : Cell := gridCell 64 26 7
theorem check2766 : PinnStaged.check cell2766 = true := by
  decide +kernel
theorem bound2766 {x y : ℝ} (h : cell2766.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2766 check2766 h
def cell2765 : Cell := gridCell 64 27 6
theorem check2765 : PinnStaged.check cell2765 = true := by
  decide +kernel
theorem bound2765 {x y : ℝ} (h : cell2765.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2765 check2765 h
def cell2764 : Cell := gridCell 64 27 7
theorem check2764 : PinnStaged.check cell2764 = true := by
  decide +kernel
theorem bound2764 {x y : ℝ} (h : cell2764.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2764 check2764 h
def RawShard0167Cells : List Cell := [cell2767, cell2766, cell2765, cell2764]
theorem RawShard0167Valid : ValidCells RawShard0167Cells := by
  intro c hc x y h
  simp only [RawShard0167Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2767 | h2766 | h2765 | h2764
  · subst c
    exact bound2767 h
  · subst c
    exact bound2766 h
  · subst c
    exact bound2765 h
  · subst c
    exact bound2764 h
#print axioms RawShard0167Valid
end PinnCertFarm
