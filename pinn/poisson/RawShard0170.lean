import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3320 : Cell := gridCell 64 30 0
theorem check3320 : PinnStaged.check cell3320 = true := by
  decide +kernel
theorem bound3320 {x y : ℝ} (h : cell3320.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3320 check3320 h
def cell3319 : Cell := gridCell 64 30 1
theorem check3319 : PinnStaged.check cell3319 = true := by
  decide +kernel
theorem bound3319 {x y : ℝ} (h : cell3319.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3319 check3319 h
def cell3318 : Cell := gridCell 64 31 0
theorem check3318 : PinnStaged.check cell3318 = true := by
  decide +kernel
theorem bound3318 {x y : ℝ} (h : cell3318.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3318 check3318 h
def cell3317 : Cell := gridCell 64 31 1
theorem check3317 : PinnStaged.check cell3317 = true := by
  decide +kernel
theorem bound3317 {x y : ℝ} (h : cell3317.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3317 check3317 h
def RawShard0170Cells : List Cell := [cell3320, cell3319, cell3318, cell3317]
theorem RawShard0170Valid : ValidCells RawShard0170Cells := by
  intro c hc x y h
  simp only [RawShard0170Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3320 | h3319 | h3318 | h3317
  · subst c
    exact bound3320 h
  · subst c
    exact bound3319 h
  · subst c
    exact bound3318 h
  · subst c
    exact bound3317 h
#print axioms RawShard0170Valid
end PinnCertFarm
