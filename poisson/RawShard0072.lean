import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell470 : Cell := gridCell 64 4 16
theorem check470 : PinnStaged.check cell470 = true := by
  decide +kernel
theorem bound470 {x y : ℝ} (h : cell470.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell470 check470 h
def cell469 : Cell := gridCell 64 4 17
theorem check469 : PinnStaged.check cell469 = true := by
  decide +kernel
theorem bound469 {x y : ℝ} (h : cell469.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell469 check469 h
def cell468 : Cell := gridCell 64 5 16
theorem check468 : PinnStaged.check cell468 = true := by
  decide +kernel
theorem bound468 {x y : ℝ} (h : cell468.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell468 check468 h
def cell467 : Cell := gridCell 64 5 17
theorem check467 : PinnStaged.check cell467 = true := by
  decide +kernel
theorem bound467 {x y : ℝ} (h : cell467.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell467 check467 h
def RawShard0072Cells : List Cell := [cell470, cell469, cell468, cell467]
theorem RawShard0072Valid : ValidCells RawShard0072Cells := by
  intro c hc x y h
  simp only [RawShard0072Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h470 | h469 | h468 | h467
  · subst c
    exact bound470 h
  · subst c
    exact bound469 h
  · subst c
    exact bound468 h
  · subst c
    exact bound467 h
#print axioms RawShard0072Valid
end PinnCertFarm
