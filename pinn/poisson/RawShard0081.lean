import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell107 : Cell := gridCell 64 0 26
theorem check107 : PinnStaged.check cell107 = true := by
  decide +kernel
theorem bound107 {x y : ℝ} (h : cell107.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell107 check107 h
def cell106 : Cell := gridCell 64 0 27
theorem check106 : PinnStaged.check cell106 = true := by
  decide +kernel
theorem bound106 {x y : ℝ} (h : cell106.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell106 check106 h
def cell105 : Cell := gridCell 64 1 26
theorem check105 : PinnStaged.check cell105 = true := by
  decide +kernel
theorem bound105 {x y : ℝ} (h : cell105.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell105 check105 h
def cell104 : Cell := gridCell 64 1 27
theorem check104 : PinnStaged.check cell104 = true := by
  decide +kernel
theorem bound104 {x y : ℝ} (h : cell104.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell104 check104 h
def RawShard0081Cells : List Cell := [cell107, cell106, cell105, cell104]
theorem RawShard0081Valid : ValidCells RawShard0081Cells := by
  intro c hc x y h
  simp only [RawShard0081Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h107 | h106 | h105 | h104
  · subst c
    exact bound107 h
  · subst c
    exact bound106 h
  · subst c
    exact bound105 h
  · subst c
    exact bound104 h
#print axioms RawShard0081Valid
end PinnCertFarm
