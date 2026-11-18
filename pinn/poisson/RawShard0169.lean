import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3324 : Cell := gridCell 64 28 2
theorem check3324 : PinnStaged.check cell3324 = true := by
  decide +kernel
theorem bound3324 {x y : ℝ} (h : cell3324.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3324 check3324 h
def cell3323 : Cell := gridCell 64 28 3
theorem check3323 : PinnStaged.check cell3323 = true := by
  decide +kernel
theorem bound3323 {x y : ℝ} (h : cell3323.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3323 check3323 h
def cell3322 : Cell := gridCell 64 29 2
theorem check3322 : PinnStaged.check cell3322 = true := by
  decide +kernel
theorem bound3322 {x y : ℝ} (h : cell3322.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3322 check3322 h
def cell3321 : Cell := gridCell 64 29 3
theorem check3321 : PinnStaged.check cell3321 = true := by
  decide +kernel
theorem bound3321 {x y : ℝ} (h : cell3321.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3321 check3321 h
def RawShard0169Cells : List Cell := [cell3324, cell3323, cell3322, cell3321]
theorem RawShard0169Valid : ValidCells RawShard0169Cells := by
  intro c hc x y h
  simp only [RawShard0169Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3324 | h3323 | h3322 | h3321
  · subst c
    exact bound3324 h
  · subst c
    exact bound3323 h
  · subst c
    exact bound3322 h
  · subst c
    exact bound3321 h
#print axioms RawShard0169Valid
end PinnCertFarm
