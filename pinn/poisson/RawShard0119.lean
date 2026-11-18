import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell927 : Cell := gridCell 64 10 30
theorem check927 : PinnStaged.check cell927 = true := by
  decide +kernel
theorem bound927 {x y : ℝ} (h : cell927.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell927 check927 h
def cell926 : Cell := gridCell 64 10 31
theorem check926 : PinnStaged.check cell926 = true := by
  decide +kernel
theorem bound926 {x y : ℝ} (h : cell926.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell926 check926 h
def cell925 : Cell := gridCell 64 11 30
theorem check925 : PinnStaged.check cell925 = true := by
  decide +kernel
theorem bound925 {x y : ℝ} (h : cell925.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell925 check925 h
def cell924 : Cell := gridCell 64 11 31
theorem check924 : PinnStaged.check cell924 = true := by
  decide +kernel
theorem bound924 {x y : ℝ} (h : cell924.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell924 check924 h
def RawShard0119Cells : List Cell := [cell927, cell926, cell925, cell924]
theorem RawShard0119Valid : ValidCells RawShard0119Cells := by
  intro c hc x y h
  simp only [RawShard0119Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h927 | h926 | h925 | h924
  · subst c
    exact bound927 h
  · subst c
    exact bound926 h
  · subst c
    exact bound925 h
  · subst c
    exact bound924 h
#print axioms RawShard0119Valid
end PinnCertFarm
