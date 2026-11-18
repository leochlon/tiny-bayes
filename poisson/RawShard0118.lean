import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell931 : Cell := gridCell 64 10 28
theorem check931 : PinnStaged.check cell931 = true := by
  decide +kernel
theorem bound931 {x y : ℝ} (h : cell931.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell931 check931 h
def cell930 : Cell := gridCell 64 10 29
theorem check930 : PinnStaged.check cell930 = true := by
  decide +kernel
theorem bound930 {x y : ℝ} (h : cell930.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell930 check930 h
def cell929 : Cell := gridCell 64 11 28
theorem check929 : PinnStaged.check cell929 = true := by
  decide +kernel
theorem bound929 {x y : ℝ} (h : cell929.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell929 check929 h
def cell928 : Cell := gridCell 64 11 29
theorem check928 : PinnStaged.check cell928 = true := by
  decide +kernel
theorem bound928 {x y : ℝ} (h : cell928.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell928 check928 h
def RawShard0118Cells : List Cell := [cell931, cell930, cell929, cell928]
theorem RawShard0118Valid : ValidCells RawShard0118Cells := by
  intro c hc x y h
  simp only [RawShard0118Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h931 | h930 | h929 | h928
  · subst c
    exact bound931 h
  · subst c
    exact bound930 h
  · subst c
    exact bound929 h
  · subst c
    exact bound928 h
#print axioms RawShard0118Valid
end PinnCertFarm
