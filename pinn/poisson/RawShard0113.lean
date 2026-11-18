import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell919 : Cell := gridCell 64 8 26
theorem check919 : PinnStaged.check cell919 = true := by
  decide +kernel
theorem bound919 {x y : ℝ} (h : cell919.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell919 check919 h
def cell918 : Cell := gridCell 64 8 27
theorem check918 : PinnStaged.check cell918 = true := by
  decide +kernel
theorem bound918 {x y : ℝ} (h : cell918.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell918 check918 h
def cell917 : Cell := gridCell 64 9 26
theorem check917 : PinnStaged.check cell917 = true := by
  decide +kernel
theorem bound917 {x y : ℝ} (h : cell917.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell917 check917 h
def cell916 : Cell := gridCell 64 9 27
theorem check916 : PinnStaged.check cell916 = true := by
  decide +kernel
theorem bound916 {x y : ℝ} (h : cell916.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell916 check916 h
def RawShard0113Cells : List Cell := [cell919, cell918, cell917, cell916]
theorem RawShard0113Valid : ValidCells RawShard0113Cells := by
  intro c hc x y h
  simp only [RawShard0113Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h919 | h918 | h917 | h916
  · subst c
    exact bound919 h
  · subst c
    exact bound918 h
  · subst c
    exact bound917 h
  · subst c
    exact bound916 h
#print axioms RawShard0113Valid
end PinnCertFarm
