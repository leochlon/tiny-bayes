import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3364 : Cell := gridCell 64 30 14
theorem check3364 : PinnStaged.check cell3364 = true := by
  decide +kernel
theorem bound3364 {x y : ℝ} (h : cell3364.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3364 check3364 h
def cell3363 : Cell := gridCell 64 30 15
theorem check3363 : PinnStaged.check cell3363 = true := by
  decide +kernel
theorem bound3363 {x y : ℝ} (h : cell3363.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3363 check3363 h
def cell3362 : Cell := gridCell 64 31 14
theorem check3362 : PinnStaged.check cell3362 = true := by
  decide +kernel
theorem bound3362 {x y : ℝ} (h : cell3362.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3362 check3362 h
def cell3361 : Cell := gridCell 64 31 15
theorem check3361 : PinnStaged.check cell3361 = true := by
  decide +kernel
theorem bound3361 {x y : ℝ} (h : cell3361.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3361 check3361 h
def RawShard0191Cells : List Cell := [cell3364, cell3363, cell3362, cell3361]
theorem RawShard0191Valid : ValidCells RawShard0191Cells := by
  intro c hc x y h
  simp only [RawShard0191Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3364 | h3363 | h3362 | h3361
  · subst c
    exact bound3364 h
  · subst c
    exact bound3363 h
  · subst c
    exact bound3362 h
  · subst c
    exact bound3361 h
#print axioms RawShard0191Valid
end PinnCertFarm
