import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4610 : Cell := gridCell 128 77 82
theorem check4610 : PinnStaged.check cell4610 = true := by
  decide +kernel
theorem bound4610 {x y : ℝ} (h : cell4610.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4610 check4610 h
def cell4609 : Cell := gridCell 128 77 83
theorem check4609 : PinnStaged.check cell4609 = true := by
  decide +kernel
theorem bound4609 {x y : ℝ} (h : cell4609.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4609 check4609 h
def cell4608 : Cell := gridCell 128 78 80
theorem check4608 : PinnStaged.check cell4608 = true := by
  decide +kernel
theorem bound4608 {x y : ℝ} (h : cell4608.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4608 check4608 h
def cell4607 : Cell := gridCell 128 78 81
theorem check4607 : PinnStaged.check cell4607 = true := by
  decide +kernel
theorem bound4607 {x y : ℝ} (h : cell4607.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4607 check4607 h
def RawShard1418Cells : List Cell := [cell4610, cell4609, cell4608, cell4607]
theorem RawShard1418Valid : ValidCells RawShard1418Cells := by
  intro c hc x y h
  simp only [RawShard1418Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4610 | h4609 | h4608 | h4607
  · subst c
    exact bound4610 h
  · subst c
    exact bound4609 h
  · subst c
    exact bound4608 h
  · subst c
    exact bound4607 h
#print axioms RawShard1418Valid
end PinnCertFarm
