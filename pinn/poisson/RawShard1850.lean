import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6350 : Cell := gridCell 128 98 87
theorem check6350 : PinnStaged.check cell6350 = true := by
  decide +kernel
theorem bound6350 {x y : ℝ} (h : cell6350.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6350 check6350 h
def cell6349 : Cell := gridCell 128 99 86
theorem check6349 : PinnStaged.check cell6349 = true := by
  decide +kernel
theorem bound6349 {x y : ℝ} (h : cell6349.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6349 check6349 h
def cell6348 : Cell := gridCell 128 99 87
theorem check6348 : PinnStaged.check cell6348 = true := by
  decide +kernel
theorem bound6348 {x y : ℝ} (h : cell6348.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6348 check6348 h
def cell6347 : Cell := gridCell 128 100 80
theorem check6347 : PinnStaged.check cell6347 = true := by
  decide +kernel
theorem bound6347 {x y : ℝ} (h : cell6347.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6347 check6347 h
def RawShard1850Cells : List Cell := [cell6350, cell6349, cell6348, cell6347]
theorem RawShard1850Valid : ValidCells RawShard1850Cells := by
  intro c hc x y h
  simp only [RawShard1850Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6350 | h6349 | h6348 | h6347
  · subst c
    exact bound6350 h
  · subst c
    exact bound6349 h
  · subst c
    exact bound6348 h
  · subst c
    exact bound6347 h
#print axioms RawShard1850Valid
end PinnCertFarm
