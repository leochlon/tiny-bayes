import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell518 : Cell := gridCell 64 4 28
theorem check518 : PinnStaged.check cell518 = true := by
  decide +kernel
theorem bound518 {x y : ℝ} (h : cell518.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell518 check518 h
def cell517 : Cell := gridCell 64 4 29
theorem check517 : PinnStaged.check cell517 = true := by
  decide +kernel
theorem bound517 {x y : ℝ} (h : cell517.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell517 check517 h
def cell516 : Cell := gridCell 64 5 28
theorem check516 : PinnStaged.check cell516 = true := by
  decide +kernel
theorem bound516 {x y : ℝ} (h : cell516.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell516 check516 h
def cell515 : Cell := gridCell 64 5 29
theorem check515 : PinnStaged.check cell515 = true := by
  decide +kernel
theorem bound515 {x y : ℝ} (h : cell515.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell515 check515 h
def RawShard0092Cells : List Cell := [cell518, cell517, cell516, cell515]
theorem RawShard0092Valid : ValidCells RawShard0092Cells := by
  intro c hc x y h
  simp only [RawShard0092Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h518 | h517 | h516 | h515
  · subst c
    exact bound518 h
  · subst c
    exact bound517 h
  · subst c
    exact bound516 h
  · subst c
    exact bound515 h
#print axioms RawShard0092Valid
end PinnCertFarm
