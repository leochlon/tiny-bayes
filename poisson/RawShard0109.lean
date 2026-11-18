import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1333 : Cell := gridCell 64 12 22
theorem check1333 : PinnStaged.check cell1333 = true := by
  decide +kernel
theorem bound1333 {x y : ℝ} (h : cell1333.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1333 check1333 h
def cell1332 : Cell := gridCell 64 12 23
theorem check1332 : PinnStaged.check cell1332 = true := by
  decide +kernel
theorem bound1332 {x y : ℝ} (h : cell1332.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1332 check1332 h
def cell1331 : Cell := gridCell 64 13 22
theorem check1331 : PinnStaged.check cell1331 = true := by
  decide +kernel
theorem bound1331 {x y : ℝ} (h : cell1331.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1331 check1331 h
def cell1330 : Cell := gridCell 64 13 23
theorem check1330 : PinnStaged.check cell1330 = true := by
  decide +kernel
theorem bound1330 {x y : ℝ} (h : cell1330.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1330 check1330 h
def RawShard0109Cells : List Cell := [cell1333, cell1332, cell1331, cell1330]
theorem RawShard0109Valid : ValidCells RawShard0109Cells := by
  intro c hc x y h
  simp only [RawShard0109Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1333 | h1332 | h1331 | h1330
  · subst c
    exact bound1333 h
  · subst c
    exact bound1332 h
  · subst c
    exact bound1331 h
  · subst c
    exact bound1330 h
#print axioms RawShard0109Valid
end PinnCertFarm
