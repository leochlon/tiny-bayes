import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell883 : Cell := gridCell 64 10 16
theorem check883 : PinnStaged.check cell883 = true := by
  decide +kernel
theorem bound883 {x y : ℝ} (h : cell883.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell883 check883 h
def cell882 : Cell := gridCell 64 10 17
theorem check882 : PinnStaged.check cell882 = true := by
  decide +kernel
theorem bound882 {x y : ℝ} (h : cell882.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell882 check882 h
def cell881 : Cell := gridCell 64 11 16
theorem check881 : PinnStaged.check cell881 = true := by
  decide +kernel
theorem bound881 {x y : ℝ} (h : cell881.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell881 check881 h
def cell880 : Cell := gridCell 64 11 17
theorem check880 : PinnStaged.check cell880 = true := by
  decide +kernel
theorem bound880 {x y : ℝ} (h : cell880.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell880 check880 h
def RawShard0098Cells : List Cell := [cell883, cell882, cell881, cell880]
theorem RawShard0098Valid : ValidCells RawShard0098Cells := by
  intro c hc x y h
  simp only [RawShard0098Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h883 | h882 | h881 | h880
  · subst c
    exact bound883 h
  · subst c
    exact bound882 h
  · subst c
    exact bound881 h
  · subst c
    exact bound880 h
#print axioms RawShard0098Valid
end PinnCertFarm
