import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4646 : Cell := gridCell 128 73 80
theorem check4646 : PinnStaged.check cell4646 = true := by
  decide +kernel
theorem bound4646 {x y : ℝ} (h : cell4646.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4646 check4646 h
def cell4645 : Cell := gridCell 128 73 81
theorem check4645 : PinnStaged.check cell4645 = true := by
  decide +kernel
theorem bound4645 {x y : ℝ} (h : cell4645.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4645 check4645 h
def cell4644 : Cell := gridCell 128 72 82
theorem check4644 : PinnStaged.check cell4644 = true := by
  decide +kernel
theorem bound4644 {x y : ℝ} (h : cell4644.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4644 check4644 h
def cell4643 : Cell := gridCell 128 72 83
theorem check4643 : PinnStaged.check cell4643 = true := by
  decide +kernel
theorem bound4643 {x y : ℝ} (h : cell4643.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4643 check4643 h
def RawShard1409Cells : List Cell := [cell4646, cell4645, cell4644, cell4643]
theorem RawShard1409Valid : ValidCells RawShard1409Cells := by
  intro c hc x y h
  simp only [RawShard1409Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4646 | h4645 | h4644 | h4643
  · subst c
    exact bound4646 h
  · subst c
    exact bound4645 h
  · subst c
    exact bound4644 h
  · subst c
    exact bound4643 h
#print axioms RawShard1409Valid
end PinnCertFarm
