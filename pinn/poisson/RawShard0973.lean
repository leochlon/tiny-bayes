import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3887 : Cell := gridCell 64 35 4
theorem check3887 : PinnStaged.check cell3887 = true := by
  decide +kernel
theorem bound3887 {x y : ℝ} (h : cell3887.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3887 check3887 h
def cell3886 : Cell := gridCell 64 35 5
theorem check3886 : PinnStaged.check cell3886 = true := by
  decide +kernel
theorem bound3886 {x y : ℝ} (h : cell3886.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3886 check3886 h
def cell3885 : Cell := gridCell 64 34 6
theorem check3885 : PinnStaged.check cell3885 = true := by
  decide +kernel
theorem bound3885 {x y : ℝ} (h : cell3885.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3885 check3885 h
def cell3884 : Cell := gridCell 64 34 7
theorem check3884 : PinnStaged.check cell3884 = true := by
  decide +kernel
theorem bound3884 {x y : ℝ} (h : cell3884.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3884 check3884 h
def RawShard0973Cells : List Cell := [cell3887, cell3886, cell3885, cell3884]
theorem RawShard0973Valid : ValidCells RawShard0973Cells := by
  intro c hc x y h
  simp only [RawShard0973Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3887 | h3886 | h3885 | h3884
  · subst c
    exact bound3887 h
  · subst c
    exact bound3886 h
  · subst c
    exact bound3885 h
  · subst c
    exact bound3884 h
#print axioms RawShard0973Valid
end PinnCertFarm
