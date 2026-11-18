import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1345 : Cell := gridCell 64 14 24
theorem check1345 : PinnStaged.check cell1345 = true := by
  decide +kernel
theorem bound1345 {x y : ℝ} (h : cell1345.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1345 check1345 h
def cell1344 : Cell := gridCell 64 14 25
theorem check1344 : PinnStaged.check cell1344 = true := by
  decide +kernel
theorem bound1344 {x y : ℝ} (h : cell1344.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1344 check1344 h
def cell1343 : Cell := gridCell 64 15 24
theorem check1343 : PinnStaged.check cell1343 = true := by
  decide +kernel
theorem bound1343 {x y : ℝ} (h : cell1343.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1343 check1343 h
def cell1342 : Cell := gridCell 64 15 25
theorem check1342 : PinnStaged.check cell1342 = true := by
  decide +kernel
theorem bound1342 {x y : ℝ} (h : cell1342.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1342 check1342 h
def RawShard0122Cells : List Cell := [cell1345, cell1344, cell1343, cell1342]
theorem RawShard0122Valid : ValidCells RawShard0122Cells := by
  intro c hc x y h
  simp only [RawShard0122Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1345 | h1344 | h1343 | h1342
  · subst c
    exact bound1345 h
  · subst c
    exact bound1344 h
  · subst c
    exact bound1343 h
  · subst c
    exact bound1342 h
#print axioms RawShard0122Valid
end PinnCertFarm
