import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4614 : Cell := gridCell 128 77 80
theorem check4614 : PinnStaged.check cell4614 = true := by
  decide +kernel
theorem bound4614 {x y : ℝ} (h : cell4614.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4614 check4614 h
def cell4613 : Cell := gridCell 128 77 81
theorem check4613 : PinnStaged.check cell4613 = true := by
  decide +kernel
theorem bound4613 {x y : ℝ} (h : cell4613.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4613 check4613 h
def cell4612 : Cell := gridCell 128 76 82
theorem check4612 : PinnStaged.check cell4612 = true := by
  decide +kernel
theorem bound4612 {x y : ℝ} (h : cell4612.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4612 check4612 h
def cell4611 : Cell := gridCell 128 76 83
theorem check4611 : PinnStaged.check cell4611 = true := by
  decide +kernel
theorem bound4611 {x y : ℝ} (h : cell4611.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4611 check4611 h
def RawShard1417Cells : List Cell := [cell4614, cell4613, cell4612, cell4611]
theorem RawShard1417Valid : ValidCells RawShard1417Cells := by
  intro c hc x y h
  simp only [RawShard1417Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4614 | h4613 | h4612 | h4611
  · subst c
    exact bound4614 h
  · subst c
    exact bound4613 h
  · subst c
    exact bound4612 h
  · subst c
    exact bound4611 h
#print axioms RawShard1417Valid
end PinnCertFarm
