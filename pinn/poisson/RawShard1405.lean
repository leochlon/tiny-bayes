import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4103 : Cell := gridCell 128 71 91
theorem check4103 : PinnStaged.check cell4103 = true := by
  decide +kernel
theorem bound4103 {x y : ℝ} (h : cell4103.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4103 check4103 h
def cell4102 : Cell := gridCell 128 68 92
theorem check4102 : PinnStaged.check cell4102 = true := by
  decide +kernel
theorem bound4102 {x y : ℝ} (h : cell4102.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4102 check4102 h
def cell4101 : Cell := gridCell 128 68 93
theorem check4101 : PinnStaged.check cell4101 = true := by
  decide +kernel
theorem bound4101 {x y : ℝ} (h : cell4101.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4101 check4101 h
def cell4100 : Cell := gridCell 128 69 92
theorem check4100 : PinnStaged.check cell4100 = true := by
  decide +kernel
theorem bound4100 {x y : ℝ} (h : cell4100.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4100 check4100 h
def RawShard1405Cells : List Cell := [cell4103, cell4102, cell4101, cell4100]
theorem RawShard1405Valid : ValidCells RawShard1405Cells := by
  intro c hc x y h
  simp only [RawShard1405Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4103 | h4102 | h4101 | h4100
  · subst c
    exact bound4103 h
  · subst c
    exact bound4102 h
  · subst c
    exact bound4101 h
  · subst c
    exact bound4100 h
#print axioms RawShard1405Valid
end PinnCertFarm
