import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3891 : Cell := gridCell 64 33 6
theorem check3891 : PinnStaged.check cell3891 = true := by
  decide +kernel
theorem bound3891 {x y : ℝ} (h : cell3891.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3891 check3891 h
def cell3890 : Cell := gridCell 64 33 7
theorem check3890 : PinnStaged.check cell3890 = true := by
  decide +kernel
theorem bound3890 {x y : ℝ} (h : cell3890.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3890 check3890 h
def cell3889 : Cell := gridCell 64 34 4
theorem check3889 : PinnStaged.check cell3889 = true := by
  decide +kernel
theorem bound3889 {x y : ℝ} (h : cell3889.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3889 check3889 h
def cell3888 : Cell := gridCell 64 34 5
theorem check3888 : PinnStaged.check cell3888 = true := by
  decide +kernel
theorem bound3888 {x y : ℝ} (h : cell3888.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3888 check3888 h
def RawShard0972Cells : List Cell := [cell3891, cell3890, cell3889, cell3888]
theorem RawShard0972Valid : ValidCells RawShard0972Cells := by
  intro c hc x y h
  simp only [RawShard0972Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3891 | h3890 | h3889 | h3888
  · subst c
    exact bound3891 h
  · subst c
    exact bound3890 h
  · subst c
    exact bound3889 h
  · subst c
    exact bound3888 h
#print axioms RawShard0972Valid
end PinnCertFarm
