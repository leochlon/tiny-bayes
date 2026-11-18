import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3340 : Cell := gridCell 64 28 6
theorem check3340 : PinnStaged.check cell3340 = true := by
  decide +kernel
theorem bound3340 {x y : ℝ} (h : cell3340.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3340 check3340 h
def cell3339 : Cell := gridCell 64 28 7
theorem check3339 : PinnStaged.check cell3339 = true := by
  decide +kernel
theorem bound3339 {x y : ℝ} (h : cell3339.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3339 check3339 h
def cell3338 : Cell := gridCell 64 29 6
theorem check3338 : PinnStaged.check cell3338 = true := by
  decide +kernel
theorem bound3338 {x y : ℝ} (h : cell3338.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3338 check3338 h
def cell3337 : Cell := gridCell 64 29 7
theorem check3337 : PinnStaged.check cell3337 = true := by
  decide +kernel
theorem bound3337 {x y : ℝ} (h : cell3337.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3337 check3337 h
def RawShard0173Cells : List Cell := [cell3340, cell3339, cell3338, cell3337]
theorem RawShard0173Valid : ValidCells RawShard0173Cells := by
  intro c hc x y h
  simp only [RawShard0173Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3340 | h3339 | h3338 | h3337
  · subst c
    exact bound3340 h
  · subst c
    exact bound3339 h
  · subst c
    exact bound3338 h
  · subst c
    exact bound3337 h
#print axioms RawShard0173Valid
end PinnCertFarm
