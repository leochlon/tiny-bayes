import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6374 : Cell := gridCell 128 96 83
theorem check6374 : PinnStaged.check cell6374 = true := by
  decide +kernel
theorem bound6374 {x y : ℝ} (h : cell6374.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6374 check6374 h
def cell6373 : Cell := gridCell 128 97 82
theorem check6373 : PinnStaged.check cell6373 = true := by
  decide +kernel
theorem bound6373 {x y : ℝ} (h : cell6373.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6373 check6373 h
def cell6372 : Cell := gridCell 128 97 83
theorem check6372 : PinnStaged.check cell6372 = true := by
  decide +kernel
theorem bound6372 {x y : ℝ} (h : cell6372.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6372 check6372 h
def cell6371 : Cell := gridCell 128 98 80
theorem check6371 : PinnStaged.check cell6371 = true := by
  decide +kernel
theorem bound6371 {x y : ℝ} (h : cell6371.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6371 check6371 h
def RawShard1844Cells : List Cell := [cell6374, cell6373, cell6372, cell6371]
theorem RawShard1844Valid : ValidCells RawShard1844Cells := by
  intro c hc x y h
  simp only [RawShard1844Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6374 | h6373 | h6372 | h6371
  · subst c
    exact bound6374 h
  · subst c
    exact bound6373 h
  · subst c
    exact bound6372 h
  · subst c
    exact bound6371 h
#print axioms RawShard1844Valid
end PinnCertFarm
