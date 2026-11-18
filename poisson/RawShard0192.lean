import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell1763 : Cell := gridCell 64 16 16
theorem check1763 : PinnStaged.check cell1763 = true := by
  decide +kernel
theorem bound1763 {x y : ℝ} (h : cell1763.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1763 check1763 h
def cell1762 : Cell := gridCell 64 16 17
theorem check1762 : PinnStaged.check cell1762 = true := by
  decide +kernel
theorem bound1762 {x y : ℝ} (h : cell1762.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1762 check1762 h
def cell1761 : Cell := gridCell 64 17 16
theorem check1761 : PinnStaged.check cell1761 = true := by
  decide +kernel
theorem bound1761 {x y : ℝ} (h : cell1761.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1761 check1761 h
def cell1760 : Cell := gridCell 64 17 17
theorem check1760 : PinnStaged.check cell1760 = true := by
  decide +kernel
theorem bound1760 {x y : ℝ} (h : cell1760.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell1760 check1760 h
def RawShard0192Cells : List Cell := [cell1763, cell1762, cell1761, cell1760]
theorem RawShard0192Valid : ValidCells RawShard0192Cells := by
  intro c hc x y h
  simp only [RawShard0192Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h1763 | h1762 | h1761 | h1760
  · subst c
    exact bound1763 h
  · subst c
    exact bound1762 h
  · subst c
    exact bound1761 h
  · subst c
    exact bound1760 h
#print axioms RawShard0192Valid
end PinnCertFarm
