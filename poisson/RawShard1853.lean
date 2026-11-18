import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6338 : Cell := gridCell 128 102 81
theorem check6338 : PinnStaged.check cell6338 = true := by
  decide +kernel
theorem bound6338 {x y : ℝ} (h : cell6338.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6338 check6338 h
def cell6337 : Cell := gridCell 128 103 80
theorem check6337 : PinnStaged.check cell6337 = true := by
  decide +kernel
theorem bound6337 {x y : ℝ} (h : cell6337.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6337 check6337 h
def cell6336 : Cell := gridCell 128 103 81
theorem check6336 : PinnStaged.check cell6336 = true := by
  decide +kernel
theorem bound6336 {x y : ℝ} (h : cell6336.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6336 check6336 h
def cell6335 : Cell := gridCell 128 102 82
theorem check6335 : PinnStaged.check cell6335 = true := by
  decide +kernel
theorem bound6335 {x y : ℝ} (h : cell6335.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6335 check6335 h
def RawShard1853Cells : List Cell := [cell6338, cell6337, cell6336, cell6335]
theorem RawShard1853Valid : ValidCells RawShard1853Cells := by
  intro c hc x y h
  simp only [RawShard1853Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6338 | h6337 | h6336 | h6335
  · subst c
    exact bound6338 h
  · subst c
    exact bound6337 h
  · subst c
    exact bound6336 h
  · subst c
    exact bound6335 h
#print axioms RawShard1853Valid
end PinnCertFarm
