import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell67 : Cell := gridCell 64 2 18
theorem check67 : PinnStaged.check cell67 = true := by
  decide +kernel
theorem bound67 {x y : ℝ} (h : cell67.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell67 check67 h
def cell66 : Cell := gridCell 64 2 19
theorem check66 : PinnStaged.check cell66 = true := by
  decide +kernel
theorem bound66 {x y : ℝ} (h : cell66.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell66 check66 h
def cell65 : Cell := gridCell 64 3 18
theorem check65 : PinnStaged.check cell65 = true := by
  decide +kernel
theorem bound65 {x y : ℝ} (h : cell65.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell65 check65 h
def cell64 : Cell := gridCell 64 3 19
theorem check64 : PinnStaged.check cell64 = true := by
  decide +kernel
theorem bound64 {x y : ℝ} (h : cell64.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell64 check64 h
def RawShard0067Cells : List Cell := [cell67, cell66, cell65, cell64]
theorem RawShard0067Valid : ValidCells RawShard0067Cells := by
  intro c hc x y h
  simp only [RawShard0067Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h67 | h66 | h65 | h64
  · subst c
    exact bound67 h
  · subst c
    exact bound66 h
  · subst c
    exact bound65 h
  · subst c
    exact bound64 h
#print axioms RawShard0067Valid
end PinnCertFarm
