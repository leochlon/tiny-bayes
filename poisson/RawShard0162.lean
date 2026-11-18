import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2755 : Cell := gridCell 64 26 0
theorem check2755 : PinnStaged.check cell2755 = true := by
  decide +kernel
theorem bound2755 {x y : ℝ} (h : cell2755.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2755 check2755 h
def cell2754 : Cell := gridCell 64 26 1
theorem check2754 : PinnStaged.check cell2754 = true := by
  decide +kernel
theorem bound2754 {x y : ℝ} (h : cell2754.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2754 check2754 h
def cell2753 : Cell := gridCell 64 27 0
theorem check2753 : PinnStaged.check cell2753 = true := by
  decide +kernel
theorem bound2753 {x y : ℝ} (h : cell2753.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2753 check2753 h
def cell2752 : Cell := gridCell 64 27 1
theorem check2752 : PinnStaged.check cell2752 = true := by
  decide +kernel
theorem bound2752 {x y : ℝ} (h : cell2752.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2752 check2752 h
def RawShard0162Cells : List Cell := [cell2755, cell2754, cell2753, cell2752]
theorem RawShard0162Valid : ValidCells RawShard0162Cells := by
  intro c hc x y h
  simp only [RawShard0162Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2755 | h2754 | h2753 | h2752
  · subst c
    exact bound2755 h
  · subst c
    exact bound2754 h
  · subst c
    exact bound2753 h
  · subst c
    exact bound2752 h
#print axioms RawShard0162Valid
end PinnCertFarm
