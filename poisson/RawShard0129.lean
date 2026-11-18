import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1695 : Cell := gridCell 64 16 2
theorem check1695 : PinnStaged.check cell1695 = true := by
  decide +kernel
theorem bound1695 {x y : ℝ} (h : cell1695.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1695 check1695 h
def cell1694 : Cell := gridCell 64 16 3
theorem check1694 : PinnStaged.check cell1694 = true := by
  decide +kernel
theorem bound1694 {x y : ℝ} (h : cell1694.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1694 check1694 h
def cell1693 : Cell := gridCell 64 17 2
theorem check1693 : PinnStaged.check cell1693 = true := by
  decide +kernel
theorem bound1693 {x y : ℝ} (h : cell1693.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1693 check1693 h
def cell1692 : Cell := gridCell 64 17 3
theorem check1692 : PinnStaged.check cell1692 = true := by
  decide +kernel
theorem bound1692 {x y : ℝ} (h : cell1692.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1692 check1692 h
def RawShard0129Cells : List Cell := [cell1695, cell1694, cell1693, cell1692]
theorem RawShard0129Valid : ValidCells RawShard0129Cells := by
  intro c hc x y h
  simp only [RawShard0129Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1695 | h1694 | h1693 | h1692
  · subst c
    exact bound1695 h
  · subst c
    exact bound1694 h
  · subst c
    exact bound1693 h
  · subst c
    exact bound1692 h
#print axioms RawShard0129Valid
end PinnCertFarm
