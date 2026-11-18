import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell103 : Cell := gridCell 64 2 24
theorem check103 : PinnStaged.check cell103 = true := by
  decide +kernel
theorem bound103 {x y : ℝ} (h : cell103.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell103 check103 h
def cell102 : Cell := gridCell 64 2 25
theorem check102 : PinnStaged.check cell102 = true := by
  decide +kernel
theorem bound102 {x y : ℝ} (h : cell102.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell102 check102 h
def cell101 : Cell := gridCell 64 3 24
theorem check101 : PinnStaged.check cell101 = true := by
  decide +kernel
theorem bound101 {x y : ℝ} (h : cell101.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell101 check101 h
def cell100 : Cell := gridCell 64 3 25
theorem check100 : PinnStaged.check cell100 = true := by
  decide +kernel
theorem bound100 {x y : ℝ} (h : cell100.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell100 check100 h
def RawShard0082Cells : List Cell := [cell103, cell102, cell101, cell100]
theorem RawShard0082Valid : ValidCells RawShard0082Cells := by
  intro c hc x y h
  simp only [RawShard0082Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h103 | h102 | h101 | h100
  · subst c
    exact bound103 h
  · subst c
    exact bound102 h
  · subst c
    exact bound101 h
  · subst c
    exact bound100 h
#print axioms RawShard0082Valid
end PinnCertFarm
