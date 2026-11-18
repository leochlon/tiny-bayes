import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1321 : Cell := gridCell 64 12 16
theorem check1321 : PinnStaged.check cell1321 = true := by
  decide +kernel
theorem bound1321 {x y : ℝ} (h : cell1321.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1321 check1321 h
def cell1320 : Cell := gridCell 64 12 17
theorem check1320 : PinnStaged.check cell1320 = true := by
  decide +kernel
theorem bound1320 {x y : ℝ} (h : cell1320.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1320 check1320 h
def cell1319 : Cell := gridCell 64 13 16
theorem check1319 : PinnStaged.check cell1319 = true := by
  decide +kernel
theorem bound1319 {x y : ℝ} (h : cell1319.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1319 check1319 h
def cell1318 : Cell := gridCell 64 13 17
theorem check1318 : PinnStaged.check cell1318 = true := by
  decide +kernel
theorem bound1318 {x y : ℝ} (h : cell1318.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1318 check1318 h
def RawShard0104Cells : List Cell := [cell1321, cell1320, cell1319, cell1318]
theorem RawShard0104Valid : ValidCells RawShard0104Cells := by
  intro c hc x y h
  simp only [RawShard0104Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1321 | h1320 | h1319 | h1318
  · subst c
    exact bound1321 h
  · subst c
    exact bound1320 h
  · subst c
    exact bound1319 h
  · subst c
    exact bound1318 h
#print axioms RawShard0104Valid
end PinnCertFarm
