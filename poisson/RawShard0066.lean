import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell71 : Cell := gridCell 64 2 16
theorem check71 : PinnStaged.check cell71 = true := by
  decide +kernel
theorem bound71 {x y : ℝ} (h : cell71.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell71 check71 h
def cell70 : Cell := gridCell 64 2 17
theorem check70 : PinnStaged.check cell70 = true := by
  decide +kernel
theorem bound70 {x y : ℝ} (h : cell70.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell70 check70 h
def cell69 : Cell := gridCell 64 3 16
theorem check69 : PinnStaged.check cell69 = true := by
  decide +kernel
theorem bound69 {x y : ℝ} (h : cell69.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell69 check69 h
def cell68 : Cell := gridCell 64 3 17
theorem check68 : PinnStaged.check cell68 = true := by
  decide +kernel
theorem bound68 {x y : ℝ} (h : cell68.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell68 check68 h
def RawShard0066Cells : List Cell := [cell71, cell70, cell69, cell68]
theorem RawShard0066Valid : ValidCells RawShard0066Cells := by
  intro c hc x y h
  simp only [RawShard0066Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h71 | h70 | h69 | h68
  · subst c
    exact bound71 h
  · subst c
    exact bound70 h
  · subst c
    exact bound69 h
  · subst c
    exact bound68 h
#print axioms RawShard0066Valid
end PinnCertFarm
