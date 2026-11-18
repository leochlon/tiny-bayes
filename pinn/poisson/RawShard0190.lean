import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3368 : Cell := gridCell 64 30 12
theorem check3368 : PinnStaged.check cell3368 = true := by
  decide +kernel
theorem bound3368 {x y : ℝ} (h : cell3368.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3368 check3368 h
def cell3367 : Cell := gridCell 64 30 13
theorem check3367 : PinnStaged.check cell3367 = true := by
  decide +kernel
theorem bound3367 {x y : ℝ} (h : cell3367.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3367 check3367 h
def cell3366 : Cell := gridCell 64 31 12
theorem check3366 : PinnStaged.check cell3366 = true := by
  decide +kernel
theorem bound3366 {x y : ℝ} (h : cell3366.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3366 check3366 h
def cell3365 : Cell := gridCell 64 31 13
theorem check3365 : PinnStaged.check cell3365 = true := by
  decide +kernel
theorem bound3365 {x y : ℝ} (h : cell3365.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3365 check3365 h
def RawShard0190Cells : List Cell := [cell3368, cell3367, cell3366, cell3365]
theorem RawShard0190Valid : ValidCells RawShard0190Cells := by
  intro c hc x y h
  simp only [RawShard0190Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3368 | h3367 | h3366 | h3365
  · subst c
    exact bound3368 h
  · subst c
    exact bound3367 h
  · subst c
    exact bound3366 h
  · subst c
    exact bound3365 h
#print axioms RawShard0190Valid
end PinnCertFarm
