import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell498 : Cell := gridCell 64 4 26
theorem check498 : PinnStaged.check cell498 = true := by
  decide +kernel
theorem bound498 {x y : ℝ} (h : cell498.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell498 check498 h
def cell497 : Cell := gridCell 64 4 27
theorem check497 : PinnStaged.check cell497 = true := by
  decide +kernel
theorem bound497 {x y : ℝ} (h : cell497.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell497 check497 h
def cell496 : Cell := gridCell 64 5 26
theorem check496 : PinnStaged.check cell496 = true := by
  decide +kernel
theorem bound496 {x y : ℝ} (h : cell496.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell496 check496 h
def cell495 : Cell := gridCell 64 5 27
theorem check495 : PinnStaged.check cell495 = true := by
  decide +kernel
theorem bound495 {x y : ℝ} (h : cell495.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell495 check495 h
def RawShard0089Cells : List Cell := [cell498, cell497, cell496, cell495]
theorem RawShard0089Valid : ValidCells RawShard0089Cells := by
  intro c hc x y h
  simp only [RawShard0089Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h498 | h497 | h496 | h495
  · subst c
    exact bound498 h
  · subst c
    exact bound497 h
  · subst c
    exact bound496 h
  · subst c
    exact bound495 h
#print axioms RawShard0089Valid
end PinnCertFarm
