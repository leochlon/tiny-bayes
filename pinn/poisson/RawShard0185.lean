import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3356 : Cell := gridCell 64 28 10
theorem check3356 : PinnStaged.check cell3356 = true := by
  decide +kernel
theorem bound3356 {x y : ℝ} (h : cell3356.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3356 check3356 h
def cell3355 : Cell := gridCell 64 28 11
theorem check3355 : PinnStaged.check cell3355 = true := by
  decide +kernel
theorem bound3355 {x y : ℝ} (h : cell3355.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3355 check3355 h
def cell3354 : Cell := gridCell 64 29 10
theorem check3354 : PinnStaged.check cell3354 = true := by
  decide +kernel
theorem bound3354 {x y : ℝ} (h : cell3354.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3354 check3354 h
def cell3353 : Cell := gridCell 64 29 11
theorem check3353 : PinnStaged.check cell3353 = true := by
  decide +kernel
theorem bound3353 {x y : ℝ} (h : cell3353.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3353 check3353 h
def RawShard0185Cells : List Cell := [cell3356, cell3355, cell3354, cell3353]
theorem RawShard0185Valid : ValidCells RawShard0185Cells := by
  intro c hc x y h
  simp only [RawShard0185Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3356 | h3355 | h3354 | h3353
  · subst c
    exact bound3356 h
  · subst c
    exact bound3355 h
  · subst c
    exact bound3354 h
  · subst c
    exact bound3353 h
#print axioms RawShard0185Valid
end PinnCertFarm
