import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3372 : Cell := gridCell 64 28 14
theorem check3372 : PinnStaged.check cell3372 = true := by
  decide +kernel
theorem bound3372 {x y : ℝ} (h : cell3372.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3372 check3372 h
def cell3371 : Cell := gridCell 64 28 15
theorem check3371 : PinnStaged.check cell3371 = true := by
  decide +kernel
theorem bound3371 {x y : ℝ} (h : cell3371.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3371 check3371 h
def cell3370 : Cell := gridCell 64 29 14
theorem check3370 : PinnStaged.check cell3370 = true := by
  decide +kernel
theorem bound3370 {x y : ℝ} (h : cell3370.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3370 check3370 h
def cell3369 : Cell := gridCell 64 29 15
theorem check3369 : PinnStaged.check cell3369 = true := by
  decide +kernel
theorem bound3369 {x y : ℝ} (h : cell3369.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3369 check3369 h
def RawShard0189Cells : List Cell := [cell3372, cell3371, cell3370, cell3369]
theorem RawShard0189Valid : ValidCells RawShard0189Cells := by
  intro c hc x y h
  simp only [RawShard0189Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3372 | h3371 | h3370 | h3369
  · subst c
    exact bound3372 h
  · subst c
    exact bound3371 h
  · subst c
    exact bound3370 h
  · subst c
    exact bound3369 h
#print axioms RawShard0189Valid
end PinnCertFarm
