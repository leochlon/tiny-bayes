import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3779 : Cell := gridCell 256 127 254
theorem check3779 : PinnStaged.check cell3779 = true := by
  decide +kernel
theorem bound3779 {x y : ℝ} (h : cell3779.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3779 check3779 h
def cell3778 : Cell := gridCell 256 127 255
theorem check3778 : PinnStaged.check cell3778 = true := by
  decide +kernel
theorem bound3778 {x y : ℝ} (h : cell3778.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3778 check3778 h
def cell3881 : Cell := gridCell 64 32 0
theorem check3881 : PinnStaged.check cell3881 = true := by
  decide +kernel
theorem bound3881 {x y : ℝ} (h : cell3881.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3881 check3881 h
def cell3880 : Cell := gridCell 64 32 1
theorem check3880 : PinnStaged.check cell3880 = true := by
  decide +kernel
theorem bound3880 {x y : ℝ} (h : cell3880.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3880 check3880 h
def RawShard0966Cells : List Cell := [cell3779, cell3778, cell3881, cell3880]
theorem RawShard0966Valid : ValidCells RawShard0966Cells := by
  intro c hc x y h
  simp only [RawShard0966Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3779 | h3778 | h3881 | h3880
  · subst c
    exact bound3779 h
  · subst c
    exact bound3778 h
  · subst c
    exact bound3881 h
  · subst c
    exact bound3880 h
#print axioms RawShard0966Valid
end PinnCertFarm
