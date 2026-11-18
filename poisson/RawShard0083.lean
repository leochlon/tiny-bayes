import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell99 : Cell := gridCell 64 2 26
theorem check99 : PinnStaged.check cell99 = true := by
  decide +kernel
theorem bound99 {x y : ℝ} (h : cell99.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell99 check99 h
def cell98 : Cell := gridCell 64 2 27
theorem check98 : PinnStaged.check cell98 = true := by
  decide +kernel
theorem bound98 {x y : ℝ} (h : cell98.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell98 check98 h
def cell97 : Cell := gridCell 64 3 26
theorem check97 : PinnStaged.check cell97 = true := by
  decide +kernel
theorem bound97 {x y : ℝ} (h : cell97.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell97 check97 h
def cell96 : Cell := gridCell 64 3 27
theorem check96 : PinnStaged.check cell96 = true := by
  decide +kernel
theorem bound96 {x y : ℝ} (h : cell96.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell96 check96 h
def RawShard0083Cells : List Cell := [cell99, cell98, cell97, cell96]
theorem RawShard0083Valid : ValidCells RawShard0083Cells := by
  intro c hc x y h
  simp only [RawShard0083Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h99 | h98 | h97 | h96
  · subst c
    exact bound99 h
  · subst c
    exact bound98 h
  · subst c
    exact bound97 h
  · subst c
    exact bound96 h
#print axioms RawShard0083Valid
end PinnCertFarm
