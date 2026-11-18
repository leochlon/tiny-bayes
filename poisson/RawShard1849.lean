import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6354 : Cell := gridCell 128 98 85
theorem check6354 : PinnStaged.check cell6354 = true := by
  decide +kernel
theorem bound6354 {x y : ℝ} (h : cell6354.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6354 check6354 h
def cell6353 : Cell := gridCell 128 99 84
theorem check6353 : PinnStaged.check cell6353 = true := by
  decide +kernel
theorem bound6353 {x y : ℝ} (h : cell6353.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6353 check6353 h
def cell6352 : Cell := gridCell 128 99 85
theorem check6352 : PinnStaged.check cell6352 = true := by
  decide +kernel
theorem bound6352 {x y : ℝ} (h : cell6352.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6352 check6352 h
def cell6351 : Cell := gridCell 128 98 86
theorem check6351 : PinnStaged.check cell6351 = true := by
  decide +kernel
theorem bound6351 {x y : ℝ} (h : cell6351.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6351 check6351 h
def RawShard1849Cells : List Cell := [cell6354, cell6353, cell6352, cell6351]
theorem RawShard1849Valid : ValidCells RawShard1849Cells := by
  intro c hc x y h
  simp only [RawShard1849Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6354 | h6353 | h6352 | h6351
  · subst c
    exact bound6354 h
  · subst c
    exact bound6353 h
  · subst c
    exact bound6352 h
  · subst c
    exact bound6351 h
#print axioms RawShard1849Valid
end PinnCertFarm
