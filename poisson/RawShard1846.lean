import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6366 : Cell := gridCell 128 98 83
theorem check6366 : PinnStaged.check cell6366 = true := by
  decide +kernel
theorem bound6366 {x y : ℝ} (h : cell6366.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6366 check6366 h
def cell6365 : Cell := gridCell 128 99 82
theorem check6365 : PinnStaged.check cell6365 = true := by
  decide +kernel
theorem bound6365 {x y : ℝ} (h : cell6365.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6365 check6365 h
def cell6364 : Cell := gridCell 128 99 83
theorem check6364 : PinnStaged.check cell6364 = true := by
  decide +kernel
theorem bound6364 {x y : ℝ} (h : cell6364.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6364 check6364 h
def cell6363 : Cell := gridCell 128 96 84
theorem check6363 : PinnStaged.check cell6363 = true := by
  decide +kernel
theorem bound6363 {x y : ℝ} (h : cell6363.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6363 check6363 h
def RawShard1846Cells : List Cell := [cell6366, cell6365, cell6364, cell6363]
theorem RawShard1846Valid : ValidCells RawShard1846Cells := by
  intro c hc x y h
  simp only [RawShard1846Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6366 | h6365 | h6364 | h6363
  · subst c
    exact bound6366 h
  · subst c
    exact bound6365 h
  · subst c
    exact bound6364 h
  · subst c
    exact bound6363 h
#print axioms RawShard1846Valid
end PinnCertFarm
