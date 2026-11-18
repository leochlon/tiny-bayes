import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3827 : Cell := gridCell 256 117 255
theorem check3827 : PinnStaged.check cell3827 = true := by
  decide +kernel
theorem bound3827 {x y : ℝ} (h : cell3827.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3827 check3827 h
def cell3826 : Cell := gridCell 128 59 126
theorem check3826 : PinnStaged.check cell3826 = true := by
  decide +kernel
theorem bound3826 {x y : ℝ} (h : cell3826.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3826 check3826 h
def cell3825 : Cell := gridCell 256 118 254
theorem check3825 : PinnStaged.check cell3825 = true := by
  decide +kernel
theorem bound3825 {x y : ℝ} (h : cell3825.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3825 check3825 h
def cell3824 : Cell := gridCell 256 118 255
theorem check3824 : PinnStaged.check cell3824 = true := by
  decide +kernel
theorem bound3824 {x y : ℝ} (h : cell3824.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3824 check3824 h
def RawShard0954Cells : List Cell := [cell3827, cell3826, cell3825, cell3824]
theorem RawShard0954Valid : ValidCells RawShard0954Cells := by
  intro c hc x y h
  simp only [RawShard0954Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3827 | h3826 | h3825 | h3824
  · subst c
    exact bound3827 h
  · subst c
    exact bound3826 h
  · subst c
    exact bound3825 h
  · subst c
    exact bound3824 h
#print axioms RawShard0954Valid
end PinnCertFarm
