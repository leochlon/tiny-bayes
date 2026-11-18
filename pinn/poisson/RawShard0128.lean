import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1699 : Cell := gridCell 64 16 0
theorem check1699 : PinnStaged.check cell1699 = true := by
  decide +kernel
theorem bound1699 {x y : ℝ} (h : cell1699.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1699 check1699 h
def cell1698 : Cell := gridCell 64 16 1
theorem check1698 : PinnStaged.check cell1698 = true := by
  decide +kernel
theorem bound1698 {x y : ℝ} (h : cell1698.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1698 check1698 h
def cell1697 : Cell := gridCell 64 17 0
theorem check1697 : PinnStaged.check cell1697 = true := by
  decide +kernel
theorem bound1697 {x y : ℝ} (h : cell1697.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1697 check1697 h
def cell1696 : Cell := gridCell 64 17 1
theorem check1696 : PinnStaged.check cell1696 = true := by
  decide +kernel
theorem bound1696 {x y : ℝ} (h : cell1696.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1696 check1696 h
def RawShard0128Cells : List Cell := [cell1699, cell1698, cell1697, cell1696]
theorem RawShard0128Valid : ValidCells RawShard0128Cells := by
  intro c hc x y h
  simp only [RawShard0128Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1699 | h1698 | h1697 | h1696
  · subst c
    exact bound1699 h
  · subst c
    exact bound1698 h
  · subst c
    exact bound1697 h
  · subst c
    exact bound1696 h
#print axioms RawShard0128Valid
end PinnCertFarm
