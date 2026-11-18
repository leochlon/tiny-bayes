import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell907 : Cell := gridCell 64 8 20
theorem check907 : PinnStaged.check cell907 = true := by
  decide +kernel
theorem bound907 {x y : ℝ} (h : cell907.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell907 check907 h
def cell906 : Cell := gridCell 64 8 21
theorem check906 : PinnStaged.check cell906 = true := by
  decide +kernel
theorem bound906 {x y : ℝ} (h : cell906.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell906 check906 h
def cell905 : Cell := gridCell 64 9 20
theorem check905 : PinnStaged.check cell905 = true := by
  decide +kernel
theorem bound905 {x y : ℝ} (h : cell905.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell905 check905 h
def cell904 : Cell := gridCell 64 9 21
theorem check904 : PinnStaged.check cell904 = true := by
  decide +kernel
theorem bound904 {x y : ℝ} (h : cell904.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell904 check904 h
def RawShard0100Cells : List Cell := [cell907, cell906, cell905, cell904]
theorem RawShard0100Valid : ValidCells RawShard0100Cells := by
  intro c hc x y h
  simp only [RawShard0100Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h907 | h906 | h905 | h904
  · subst c
    exact bound907 h
  · subst c
    exact bound906 h
  · subst c
    exact bound905 h
  · subst c
    exact bound904 h
#print axioms RawShard0100Valid
end PinnCertFarm
