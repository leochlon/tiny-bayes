import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3352 : Cell := gridCell 64 30 8
theorem check3352 : PinnStaged.check cell3352 = true := by
  decide +kernel
theorem bound3352 {x y : ℝ} (h : cell3352.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3352 check3352 h
def cell3351 : Cell := gridCell 64 30 9
theorem check3351 : PinnStaged.check cell3351 = true := by
  decide +kernel
theorem bound3351 {x y : ℝ} (h : cell3351.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3351 check3351 h
def cell3350 : Cell := gridCell 64 31 8
theorem check3350 : PinnStaged.check cell3350 = true := by
  decide +kernel
theorem bound3350 {x y : ℝ} (h : cell3350.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3350 check3350 h
def cell3349 : Cell := gridCell 64 31 9
theorem check3349 : PinnStaged.check cell3349 = true := by
  decide +kernel
theorem bound3349 {x y : ℝ} (h : cell3349.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3349 check3349 h
def RawShard0186Cells : List Cell := [cell3352, cell3351, cell3350, cell3349]
theorem RawShard0186Valid : ValidCells RawShard0186Cells := by
  intro c hc x y h
  simp only [RawShard0186Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3352 | h3351 | h3350 | h3349
  · subst c
    exact bound3352 h
  · subst c
    exact bound3351 h
  · subst c
    exact bound3350 h
  · subst c
    exact bound3349 h
#print axioms RawShard0186Valid
end PinnCertFarm
