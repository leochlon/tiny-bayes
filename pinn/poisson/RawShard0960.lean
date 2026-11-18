import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3803 : Cell := gridCell 128 61 124
theorem check3803 : PinnStaged.check cell3803 = true := by
  decide +kernel
theorem bound3803 {x y : ℝ} (h : cell3803.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3803 check3803 h
def cell3802 : Cell := gridCell 128 61 125
theorem check3802 : PinnStaged.check cell3802 = true := by
  decide +kernel
theorem bound3802 {x y : ℝ} (h : cell3802.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3802 check3802 h
def cell3801 : Cell := gridCell 128 60 126
theorem check3801 : PinnStaged.check cell3801 = true := by
  decide +kernel
theorem bound3801 {x y : ℝ} (h : cell3801.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3801 check3801 h
def cell3800 : Cell := gridCell 256 120 254
theorem check3800 : PinnStaged.check cell3800 = true := by
  decide +kernel
theorem bound3800 {x y : ℝ} (h : cell3800.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3800 check3800 h
def RawShard0960Cells : List Cell := [cell3803, cell3802, cell3801, cell3800]
theorem RawShard0960Valid : ValidCells RawShard0960Cells := by
  intro c hc x y h
  simp only [RawShard0960Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3803 | h3802 | h3801 | h3800
  · subst c
    exact bound3803 h
  · subst c
    exact bound3802 h
  · subst c
    exact bound3801 h
  · subst c
    exact bound3800 h
#print axioms RawShard0960Valid
end PinnCertFarm
