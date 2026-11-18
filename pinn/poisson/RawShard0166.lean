import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell2771 : Cell := gridCell 64 26 4
theorem check2771 : PinnStaged.check cell2771 = true := by
  decide +kernel
theorem bound2771 {x y : ℝ} (h : cell2771.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2771 check2771 h
def cell2770 : Cell := gridCell 64 26 5
theorem check2770 : PinnStaged.check cell2770 = true := by
  decide +kernel
theorem bound2770 {x y : ℝ} (h : cell2770.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2770 check2770 h
def cell2769 : Cell := gridCell 64 27 4
theorem check2769 : PinnStaged.check cell2769 = true := by
  decide +kernel
theorem bound2769 {x y : ℝ} (h : cell2769.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2769 check2769 h
def cell2768 : Cell := gridCell 64 27 5
theorem check2768 : PinnStaged.check cell2768 = true := by
  decide +kernel
theorem bound2768 {x y : ℝ} (h : cell2768.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell2768 check2768 h
def RawShard0166Cells : List Cell := [cell2771, cell2770, cell2769, cell2768]
theorem RawShard0166Valid : ValidCells RawShard0166Cells := by
  intro c hc x y h
  simp only [RawShard0166Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h2771 | h2770 | h2769 | h2768
  · subst c
    exact bound2771 h
  · subst c
    exact bound2770 h
  · subst c
    exact bound2769 h
  · subst c
    exact bound2768 h
#print axioms RawShard0166Valid
end PinnCertFarm
