import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3895 : Cell := gridCell 64 33 4
theorem check3895 : PinnStaged.check cell3895 = true := by
  decide +kernel
theorem bound3895 {x y : ℝ} (h : cell3895.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3895 check3895 h
def cell3894 : Cell := gridCell 64 33 5
theorem check3894 : PinnStaged.check cell3894 = true := by
  decide +kernel
theorem bound3894 {x y : ℝ} (h : cell3894.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3894 check3894 h
def cell3893 : Cell := gridCell 64 32 6
theorem check3893 : PinnStaged.check cell3893 = true := by
  decide +kernel
theorem bound3893 {x y : ℝ} (h : cell3893.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3893 check3893 h
def cell3892 : Cell := gridCell 64 32 7
theorem check3892 : PinnStaged.check cell3892 = true := by
  decide +kernel
theorem bound3892 {x y : ℝ} (h : cell3892.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3892 check3892 h
def RawShard0971Cells : List Cell := [cell3895, cell3894, cell3893, cell3892]
theorem RawShard0971Valid : ValidCells RawShard0971Cells := by
  intro c hc x y h
  simp only [RawShard0971Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3895 | h3894 | h3893 | h3892
  · subst c
    exact bound3895 h
  · subst c
    exact bound3894 h
  · subst c
    exact bound3893 h
  · subst c
    exact bound3892 h
#print axioms RawShard0971Valid
end PinnCertFarm
