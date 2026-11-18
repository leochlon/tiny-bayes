import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell4618 : Cell := gridCell 128 75 86
theorem check4618 : PinnStaged.check cell4618 = true := by
  decide +kernel
theorem bound4618 {x y : ℝ} (h : cell4618.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4618 check4618 h
def cell4617 : Cell := gridCell 128 75 87
theorem check4617 : PinnStaged.check cell4617 = true := by
  decide +kernel
theorem bound4617 {x y : ℝ} (h : cell4617.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4617 check4617 h
def cell4616 : Cell := gridCell 128 76 80
theorem check4616 : PinnStaged.check cell4616 = true := by
  decide +kernel
theorem bound4616 {x y : ℝ} (h : cell4616.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4616 check4616 h
def cell4615 : Cell := gridCell 128 76 81
theorem check4615 : PinnStaged.check cell4615 = true := by
  decide +kernel
theorem bound4615 {x y : ℝ} (h : cell4615.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell4615 check4615 h
def RawShard1416Cells : List Cell := [cell4618, cell4617, cell4616, cell4615]
theorem RawShard1416Valid : ValidCells RawShard1416Cells := by
  intro c hc x y h
  simp only [RawShard1416Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h4618 | h4617 | h4616 | h4615
  · subst c
    exact bound4618 h
  · subst c
    exact bound4617 h
  · subst c
    exact bound4616 h
  · subst c
    exact bound4615 h
#print axioms RawShard1416Valid
end PinnCertFarm
