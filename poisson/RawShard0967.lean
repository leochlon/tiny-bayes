import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3879 : Cell := gridCell 64 33 0
theorem check3879 : PinnStaged.check cell3879 = true := by
  decide +kernel
theorem bound3879 {x y : ℝ} (h : cell3879.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3879 check3879 h
def cell3878 : Cell := gridCell 64 33 1
theorem check3878 : PinnStaged.check cell3878 = true := by
  decide +kernel
theorem bound3878 {x y : ℝ} (h : cell3878.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3878 check3878 h
def cell3877 : Cell := gridCell 64 32 2
theorem check3877 : PinnStaged.check cell3877 = true := by
  decide +kernel
theorem bound3877 {x y : ℝ} (h : cell3877.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3877 check3877 h
def cell3876 : Cell := gridCell 64 32 3
theorem check3876 : PinnStaged.check cell3876 = true := by
  decide +kernel
theorem bound3876 {x y : ℝ} (h : cell3876.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3876 check3876 h
def RawShard0967Cells : List Cell := [cell3879, cell3878, cell3877, cell3876]
theorem RawShard0967Valid : ValidCells RawShard0967Cells := by
  intro c hc x y h
  simp only [RawShard0967Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3879 | h3878 | h3877 | h3876
  · subst c
    exact bound3879 h
  · subst c
    exact bound3878 h
  · subst c
    exact bound3877 h
  · subst c
    exact bound3876 h
#print axioms RawShard0967Valid
end PinnCertFarm
