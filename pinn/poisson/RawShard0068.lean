import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell95 : Cell := gridCell 64 0 20
theorem check95 : PinnStaged.check cell95 = true := by
  decide +kernel
theorem bound95 {x y : ℝ} (h : cell95.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell95 check95 h
def cell94 : Cell := gridCell 64 0 21
theorem check94 : PinnStaged.check cell94 = true := by
  decide +kernel
theorem bound94 {x y : ℝ} (h : cell94.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell94 check94 h
def cell93 : Cell := gridCell 64 1 20
theorem check93 : PinnStaged.check cell93 = true := by
  decide +kernel
theorem bound93 {x y : ℝ} (h : cell93.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell93 check93 h
def cell92 : Cell := gridCell 64 1 21
theorem check92 : PinnStaged.check cell92 = true := by
  decide +kernel
theorem bound92 {x y : ℝ} (h : cell92.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell92 check92 h
def RawShard0068Cells : List Cell := [cell95, cell94, cell93, cell92]
theorem RawShard0068Valid : ValidCells RawShard0068Cells := by
  intro c hc x y h
  simp only [RawShard0068Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h95 | h94 | h93 | h92
  · subst c
    exact bound95 h
  · subst c
    exact bound94 h
  · subst c
    exact bound93 h
  · subst c
    exact bound92 h
#print axioms RawShard0068Valid
end PinnCertFarm
