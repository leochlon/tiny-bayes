import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1353 : Cell := gridCell 64 12 24
theorem check1353 : PinnStaged.check cell1353 = true := by
  decide +kernel
theorem bound1353 {x y : ℝ} (h : cell1353.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1353 check1353 h
def cell1352 : Cell := gridCell 64 12 25
theorem check1352 : PinnStaged.check cell1352 = true := by
  decide +kernel
theorem bound1352 {x y : ℝ} (h : cell1352.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1352 check1352 h
def cell1351 : Cell := gridCell 64 13 24
theorem check1351 : PinnStaged.check cell1351 = true := by
  decide +kernel
theorem bound1351 {x y : ℝ} (h : cell1351.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1351 check1351 h
def cell1350 : Cell := gridCell 64 13 25
theorem check1350 : PinnStaged.check cell1350 = true := by
  decide +kernel
theorem bound1350 {x y : ℝ} (h : cell1350.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1350 check1350 h
def RawShard0120Cells : List Cell := [cell1353, cell1352, cell1351, cell1350]
theorem RawShard0120Valid : ValidCells RawShard0120Cells := by
  intro c hc x y h
  simp only [RawShard0120Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1353 | h1352 | h1351 | h1350
  · subst c
    exact bound1353 h
  · subst c
    exact bound1352 h
  · subst c
    exact bound1351 h
  · subst c
    exact bound1350 h
#print axioms RawShard0120Valid
end PinnCertFarm
