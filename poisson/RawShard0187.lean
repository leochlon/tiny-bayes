import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3348 : Cell := gridCell 64 30 10
theorem check3348 : PinnStaged.check cell3348 = true := by
  decide +kernel
theorem bound3348 {x y : ℝ} (h : cell3348.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3348 check3348 h
def cell3347 : Cell := gridCell 64 30 11
theorem check3347 : PinnStaged.check cell3347 = true := by
  decide +kernel
theorem bound3347 {x y : ℝ} (h : cell3347.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3347 check3347 h
def cell3346 : Cell := gridCell 64 31 10
theorem check3346 : PinnStaged.check cell3346 = true := by
  decide +kernel
theorem bound3346 {x y : ℝ} (h : cell3346.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3346 check3346 h
def cell3345 : Cell := gridCell 64 31 11
theorem check3345 : PinnStaged.check cell3345 = true := by
  decide +kernel
theorem bound3345 {x y : ℝ} (h : cell3345.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3345 check3345 h
def RawShard0187Cells : List Cell := [cell3348, cell3347, cell3346, cell3345]
theorem RawShard0187Valid : ValidCells RawShard0187Cells := by
  intro c hc x y h
  simp only [RawShard0187Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3348 | h3347 | h3346 | h3345
  · subst c
    exact bound3348 h
  · subst c
    exact bound3347 h
  · subst c
    exact bound3346 h
  · subst c
    exact bound3345 h
#print axioms RawShard0187Valid
end PinnCertFarm
