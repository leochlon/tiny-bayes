import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell91 : Cell := gridCell 64 0 22
theorem check91 : PinnStaged.check cell91 = true := by
  decide +kernel
theorem bound91 {x y : ℝ} (h : cell91.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell91 check91 h
def cell90 : Cell := gridCell 64 0 23
theorem check90 : PinnStaged.check cell90 = true := by
  decide +kernel
theorem bound90 {x y : ℝ} (h : cell90.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell90 check90 h
def cell89 : Cell := gridCell 64 1 22
theorem check89 : PinnStaged.check cell89 = true := by
  decide +kernel
theorem bound89 {x y : ℝ} (h : cell89.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell89 check89 h
def cell88 : Cell := gridCell 64 1 23
theorem check88 : PinnStaged.check cell88 = true := by
  decide +kernel
theorem bound88 {x y : ℝ} (h : cell88.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell88 check88 h
def RawShard0069Cells : List Cell := [cell91, cell90, cell89, cell88]
theorem RawShard0069Valid : ValidCells RawShard0069Cells := by
  intro c hc x y h
  simp only [RawShard0069Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h91 | h90 | h89 | h88
  · subst c
    exact bound91 h
  · subst c
    exact bound90 h
  · subst c
    exact bound89 h
  · subst c
    exact bound88 h
#print axioms RawShard0069Valid
end PinnCertFarm
