import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2751 : Cell := gridCell 64 26 2
theorem check2751 : PinnStaged.check cell2751 = true := by
  decide +kernel
theorem bound2751 {x y : ℝ} (h : cell2751.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2751 check2751 h
def cell2750 : Cell := gridCell 64 26 3
theorem check2750 : PinnStaged.check cell2750 = true := by
  decide +kernel
theorem bound2750 {x y : ℝ} (h : cell2750.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2750 check2750 h
def cell2749 : Cell := gridCell 64 27 2
theorem check2749 : PinnStaged.check cell2749 = true := by
  decide +kernel
theorem bound2749 {x y : ℝ} (h : cell2749.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2749 check2749 h
def cell2748 : Cell := gridCell 64 27 3
theorem check2748 : PinnStaged.check cell2748 = true := by
  decide +kernel
theorem bound2748 {x y : ℝ} (h : cell2748.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2748 check2748 h
def RawShard0163Cells : List Cell := [cell2751, cell2750, cell2749, cell2748]
theorem RawShard0163Valid : ValidCells RawShard0163Cells := by
  intro c hc x y h
  simp only [RawShard0163Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2751 | h2750 | h2749 | h2748
  · subst c
    exact bound2751 h
  · subst c
    exact bound2750 h
  · subst c
    exact bound2749 h
  · subst c
    exact bound2748 h
#print axioms RawShard0163Valid
end PinnCertFarm
