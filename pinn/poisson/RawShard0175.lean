import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell3332 : Cell := gridCell 64 30 6
theorem check3332 : PinnStaged.check cell3332 = true := by
  decide +kernel
theorem bound3332 {x y : ℝ} (h : cell3332.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3332 check3332 h
def cell3331 : Cell := gridCell 64 30 7
theorem check3331 : PinnStaged.check cell3331 = true := by
  decide +kernel
theorem bound3331 {x y : ℝ} (h : cell3331.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3331 check3331 h
def cell3330 : Cell := gridCell 64 31 6
theorem check3330 : PinnStaged.check cell3330 = true := by
  decide +kernel
theorem bound3330 {x y : ℝ} (h : cell3330.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3330 check3330 h
def cell3329 : Cell := gridCell 64 31 7
theorem check3329 : PinnStaged.check cell3329 = true := by
  decide +kernel
theorem bound3329 {x y : ℝ} (h : cell3329.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell3329 check3329 h
def RawShard0175Cells : List Cell := [cell3332, cell3331, cell3330, cell3329]
theorem RawShard0175Valid : ValidCells RawShard0175Cells := by
  intro c hc x y h
  simp only [RawShard0175Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h3332 | h3331 | h3330 | h3329
  · subst c
    exact bound3332 h
  · subst c
    exact bound3331 h
  · subst c
    exact bound3330 h
  · subst c
    exact bound3329 h
#print axioms RawShard0175Valid
end PinnCertFarm
