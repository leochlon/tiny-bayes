import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell879 : Cell := gridCell 64 10 18
theorem check879 : PinnStaged.check cell879 = true := by
  decide +kernel
theorem bound879 {x y : ℝ} (h : cell879.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell879 check879 h
def cell878 : Cell := gridCell 64 10 19
theorem check878 : PinnStaged.check cell878 = true := by
  decide +kernel
theorem bound878 {x y : ℝ} (h : cell878.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell878 check878 h
def cell877 : Cell := gridCell 64 11 18
theorem check877 : PinnStaged.check cell877 = true := by
  decide +kernel
theorem bound877 {x y : ℝ} (h : cell877.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell877 check877 h
def cell876 : Cell := gridCell 64 11 19
theorem check876 : PinnStaged.check cell876 = true := by
  decide +kernel
theorem bound876 {x y : ℝ} (h : cell876.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell876 check876 h
def RawShard0099Cells : List Cell := [cell879, cell878, cell877, cell876]
theorem RawShard0099Valid : ValidCells RawShard0099Cells := by
  intro c hc x y h
  simp only [RawShard0099Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h879 | h878 | h877 | h876
  · subst c
    exact bound879 h
  · subst c
    exact bound878 h
  · subst c
    exact bound877 h
  · subst c
    exact bound876 h
#print axioms RawShard0099Valid
end PinnCertFarm
