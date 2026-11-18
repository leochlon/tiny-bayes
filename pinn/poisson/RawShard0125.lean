import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1365 : Cell := gridCell 64 12 30
theorem check1365 : PinnStaged.check cell1365 = true := by
  decide +kernel
theorem bound1365 {x y : ℝ} (h : cell1365.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1365 check1365 h
def cell1364 : Cell := gridCell 64 12 31
theorem check1364 : PinnStaged.check cell1364 = true := by
  decide +kernel
theorem bound1364 {x y : ℝ} (h : cell1364.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1364 check1364 h
def cell1363 : Cell := gridCell 64 13 30
theorem check1363 : PinnStaged.check cell1363 = true := by
  decide +kernel
theorem bound1363 {x y : ℝ} (h : cell1363.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1363 check1363 h
def cell1362 : Cell := gridCell 64 13 31
theorem check1362 : PinnStaged.check cell1362 = true := by
  decide +kernel
theorem bound1362 {x y : ℝ} (h : cell1362.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1362 check1362 h
def RawShard0125Cells : List Cell := [cell1365, cell1364, cell1363, cell1362]
theorem RawShard0125Valid : ValidCells RawShard0125Cells := by
  intro c hc x y h
  simp only [RawShard0125Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1365 | h1364 | h1363 | h1362
  · subst c
    exact bound1365 h
  · subst c
    exact bound1364 h
  · subst c
    exact bound1363 h
  · subst c
    exact bound1362 h
#print axioms RawShard0125Valid
end PinnCertFarm
