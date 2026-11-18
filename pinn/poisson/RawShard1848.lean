import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6358 : Cell := gridCell 128 96 87
theorem check6358 : PinnStaged.check cell6358 = true := by
  decide +kernel
theorem bound6358 {x y : ℝ} (h : cell6358.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6358 check6358 h
def cell6357 : Cell := gridCell 128 97 86
theorem check6357 : PinnStaged.check cell6357 = true := by
  decide +kernel
theorem bound6357 {x y : ℝ} (h : cell6357.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6357 check6357 h
def cell6356 : Cell := gridCell 128 97 87
theorem check6356 : PinnStaged.check cell6356 = true := by
  decide +kernel
theorem bound6356 {x y : ℝ} (h : cell6356.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6356 check6356 h
def cell6355 : Cell := gridCell 128 98 84
theorem check6355 : PinnStaged.check cell6355 = true := by
  decide +kernel
theorem bound6355 {x y : ℝ} (h : cell6355.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6355 check6355 h
def RawShard1848Cells : List Cell := [cell6358, cell6357, cell6356, cell6355]
theorem RawShard1848Valid : ValidCells RawShard1848Cells := by
  intro c hc x y h
  simp only [RawShard1848Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6358 | h6357 | h6356 | h6355
  · subst c
    exact bound6358 h
  · subst c
    exact bound6357 h
  · subst c
    exact bound6356 h
  · subst c
    exact bound6355 h
#print axioms RawShard1848Valid
end PinnCertFarm
