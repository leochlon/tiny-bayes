import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3791 : Cell := gridCell 128 62 124
theorem check3791 : PinnStaged.check cell3791 = true := by
  decide +kernel
theorem bound3791 {x y : ℝ} (h : cell3791.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3791 check3791 h
def cell3790 : Cell := gridCell 128 62 125
theorem check3790 : PinnStaged.check cell3790 = true := by
  decide +kernel
theorem bound3790 {x y : ℝ} (h : cell3790.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3790 check3790 h
def cell3789 : Cell := gridCell 128 63 124
theorem check3789 : PinnStaged.check cell3789 = true := by
  decide +kernel
theorem bound3789 {x y : ℝ} (h : cell3789.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3789 check3789 h
def cell3788 : Cell := gridCell 128 63 125
theorem check3788 : PinnStaged.check cell3788 = true := by
  decide +kernel
theorem bound3788 {x y : ℝ} (h : cell3788.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3788 check3788 h
def RawShard0963Cells : List Cell := [cell3791, cell3790, cell3789, cell3788]
theorem RawShard0963Valid : ValidCells RawShard0963Cells := by
  intro c hc x y h
  simp only [RawShard0963Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3791 | h3790 | h3789 | h3788
  · subst c
    exact bound3791 h
  · subst c
    exact bound3790 h
  · subst c
    exact bound3789 h
  · subst c
    exact bound3788 h
#print axioms RawShard0963Valid
end PinnCertFarm
