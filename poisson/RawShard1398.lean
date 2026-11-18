import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4131 : Cell := gridCell 128 66 91
theorem check4131 : PinnStaged.check cell4131 = true := by
  decide +kernel
theorem bound4131 {x y : ℝ} (h : cell4131.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4131 check4131 h
def cell4130 : Cell := gridCell 128 67 90
theorem check4130 : PinnStaged.check cell4130 = true := by
  decide +kernel
theorem bound4130 {x y : ℝ} (h : cell4130.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4130 check4130 h
def cell4129 : Cell := gridCell 128 67 91
theorem check4129 : PinnStaged.check cell4129 = true := by
  decide +kernel
theorem bound4129 {x y : ℝ} (h : cell4129.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4129 check4129 h
def cell4128 : Cell := gridCell 128 64 92
theorem check4128 : PinnStaged.check cell4128 = true := by
  decide +kernel
theorem bound4128 {x y : ℝ} (h : cell4128.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4128 check4128 h
def RawShard1398Cells : List Cell := [cell4131, cell4130, cell4129, cell4128]
theorem RawShard1398Valid : ValidCells RawShard1398Cells := by
  intro c hc x y h
  simp only [RawShard1398Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4131 | h4130 | h4129 | h4128
  · subst c
    exact bound4131 h
  · subst c
    exact bound4130 h
  · subst c
    exact bound4129 h
  · subst c
    exact bound4128 h
#print axioms RawShard1398Valid
end PinnCertFarm
