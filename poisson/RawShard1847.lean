import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6362 : Cell := gridCell 128 96 85
theorem check6362 : PinnStaged.check cell6362 = true := by
  decide +kernel
theorem bound6362 {x y : ℝ} (h : cell6362.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6362 check6362 h
def cell6361 : Cell := gridCell 128 97 84
theorem check6361 : PinnStaged.check cell6361 = true := by
  decide +kernel
theorem bound6361 {x y : ℝ} (h : cell6361.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6361 check6361 h
def cell6360 : Cell := gridCell 128 97 85
theorem check6360 : PinnStaged.check cell6360 = true := by
  decide +kernel
theorem bound6360 {x y : ℝ} (h : cell6360.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6360 check6360 h
def cell6359 : Cell := gridCell 128 96 86
theorem check6359 : PinnStaged.check cell6359 = true := by
  decide +kernel
theorem bound6359 {x y : ℝ} (h : cell6359.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6359 check6359 h
def RawShard1847Cells : List Cell := [cell6362, cell6361, cell6360, cell6359]
theorem RawShard1847Valid : ValidCells RawShard1847Cells := by
  intro c hc x y h
  simp only [RawShard1847Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6362 | h6361 | h6360 | h6359
  · subst c
    exact bound6362 h
  · subst c
    exact bound6361 h
  · subst c
    exact bound6360 h
  · subst c
    exact bound6359 h
#print axioms RawShard1847Valid
end PinnCertFarm
