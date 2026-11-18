import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell119 : Cell := gridCell 64 2 28
theorem check119 : PinnStaged.check cell119 = true := by
  decide +kernel
theorem bound119 {x y : ℝ} (h : cell119.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell119 check119 h
def cell118 : Cell := gridCell 64 2 29
theorem check118 : PinnStaged.check cell118 = true := by
  decide +kernel
theorem bound118 {x y : ℝ} (h : cell118.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell118 check118 h
def cell117 : Cell := gridCell 64 3 28
theorem check117 : PinnStaged.check cell117 = true := by
  decide +kernel
theorem bound117 {x y : ℝ} (h : cell117.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell117 check117 h
def cell116 : Cell := gridCell 64 3 29
theorem check116 : PinnStaged.check cell116 = true := by
  decide +kernel
theorem bound116 {x y : ℝ} (h : cell116.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell116 check116 h
def RawShard0086Cells : List Cell := [cell119, cell118, cell117, cell116]
theorem RawShard0086Valid : ValidCells RawShard0086Cells := by
  intro c hc x y h
  simp only [RawShard0086Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h119 | h118 | h117 | h116
  · subst c
    exact bound119 h
  · subst c
    exact bound118 h
  · subst c
    exact bound117 h
  · subst c
    exact bound116 h
#print axioms RawShard0086Valid
end PinnCertFarm
