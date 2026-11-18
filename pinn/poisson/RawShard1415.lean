import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4622 : Cell := gridCell 128 75 84
theorem check4622 : PinnStaged.check cell4622 = true := by
  decide +kernel
theorem bound4622 {x y : ℝ} (h : cell4622.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4622 check4622 h
def cell4621 : Cell := gridCell 128 75 85
theorem check4621 : PinnStaged.check cell4621 = true := by
  decide +kernel
theorem bound4621 {x y : ℝ} (h : cell4621.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4621 check4621 h
def cell4620 : Cell := gridCell 128 74 86
theorem check4620 : PinnStaged.check cell4620 = true := by
  decide +kernel
theorem bound4620 {x y : ℝ} (h : cell4620.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4620 check4620 h
def cell4619 : Cell := gridCell 128 74 87
theorem check4619 : PinnStaged.check cell4619 = true := by
  decide +kernel
theorem bound4619 {x y : ℝ} (h : cell4619.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4619 check4619 h
def RawShard1415Cells : List Cell := [cell4622, cell4621, cell4620, cell4619]
theorem RawShard1415Valid : ValidCells RawShard1415Cells := by
  intro c hc x y h
  simp only [RawShard1415Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4622 | h4621 | h4620 | h4619
  · subst c
    exact bound4622 h
  · subst c
    exact bound4621 h
  · subst c
    exact bound4620 h
  · subst c
    exact bound4619 h
#print axioms RawShard1415Valid
end PinnCertFarm
