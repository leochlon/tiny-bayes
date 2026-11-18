import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6330 : Cell := gridCell 128 100 85
theorem check6330 : PinnStaged.check cell6330 = true := by
  decide +kernel
theorem bound6330 {x y : ℝ} (h : cell6330.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6330 check6330 h
def cell6329 : Cell := gridCell 128 101 84
theorem check6329 : PinnStaged.check cell6329 = true := by
  decide +kernel
theorem bound6329 {x y : ℝ} (h : cell6329.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6329 check6329 h
def cell6328 : Cell := gridCell 128 101 85
theorem check6328 : PinnStaged.check cell6328 = true := by
  decide +kernel
theorem bound6328 {x y : ℝ} (h : cell6328.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6328 check6328 h
def cell6327 : Cell := gridCell 128 100 86
theorem check6327 : PinnStaged.check cell6327 = true := by
  decide +kernel
theorem bound6327 {x y : ℝ} (h : cell6327.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6327 check6327 h
def RawShard1855Cells : List Cell := [cell6330, cell6329, cell6328, cell6327]
theorem RawShard1855Valid : ValidCells RawShard1855Cells := by
  intro c hc x y h
  simp only [RawShard1855Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6330 | h6329 | h6328 | h6327
  · subst c
    exact bound6330 h
  · subst c
    exact bound6329 h
  · subst c
    exact bound6328 h
  · subst c
    exact bound6327 h
#print axioms RawShard1855Valid
end PinnCertFarm
