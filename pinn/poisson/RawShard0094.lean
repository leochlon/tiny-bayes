import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell510 : Cell := gridCell 64 6 28
theorem check510 : PinnStaged.check cell510 = true := by
  decide +kernel
theorem bound510 {x y : ℝ} (h : cell510.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell510 check510 h
def cell509 : Cell := gridCell 64 6 29
theorem check509 : PinnStaged.check cell509 = true := by
  decide +kernel
theorem bound509 {x y : ℝ} (h : cell509.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell509 check509 h
def cell508 : Cell := gridCell 64 7 28
theorem check508 : PinnStaged.check cell508 = true := by
  decide +kernel
theorem bound508 {x y : ℝ} (h : cell508.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell508 check508 h
def cell507 : Cell := gridCell 64 7 29
theorem check507 : PinnStaged.check cell507 = true := by
  decide +kernel
theorem bound507 {x y : ℝ} (h : cell507.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell507 check507 h
def RawShard0094Cells : List Cell := [cell510, cell509, cell508, cell507]
theorem RawShard0094Valid : ValidCells RawShard0094Cells := by
  intro c hc x y h
  simp only [RawShard0094Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h510 | h509 | h508 | h507
  · subst c
    exact bound510 h
  · subst c
    exact bound509 h
  · subst c
    exact bound508 h
  · subst c
    exact bound507 h
#print axioms RawShard0094Valid
end PinnCertFarm
