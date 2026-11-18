import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell895 : Cell := gridCell 64 10 22
theorem check895 : PinnStaged.check cell895 = true := by
  decide +kernel
theorem bound895 {x y : ℝ} (h : cell895.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell895 check895 h
def cell894 : Cell := gridCell 64 10 23
theorem check894 : PinnStaged.check cell894 = true := by
  decide +kernel
theorem bound894 {x y : ℝ} (h : cell894.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell894 check894 h
def cell893 : Cell := gridCell 64 11 22
theorem check893 : PinnStaged.check cell893 = true := by
  decide +kernel
theorem bound893 {x y : ℝ} (h : cell893.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell893 check893 h
def cell892 : Cell := gridCell 64 11 23
theorem check892 : PinnStaged.check cell892 = true := by
  decide +kernel
theorem bound892 {x y : ℝ} (h : cell892.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell892 check892 h
def RawShard0103Cells : List Cell := [cell895, cell894, cell893, cell892]
theorem RawShard0103Valid : ValidCells RawShard0103Cells := by
  intro c hc x y h
  simp only [RawShard0103Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h895 | h894 | h893 | h892
  · subst c
    exact bound895 h
  · subst c
    exact bound894 h
  · subst c
    exact bound893 h
  · subst c
    exact bound892 h
#print axioms RawShard0103Valid
end PinnCertFarm
