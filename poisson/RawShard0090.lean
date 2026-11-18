import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell494 : Cell := gridCell 64 6 24
theorem check494 : PinnStaged.check cell494 = true := by
  decide +kernel
theorem bound494 {x y : ℝ} (h : cell494.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell494 check494 h
def cell493 : Cell := gridCell 64 6 25
theorem check493 : PinnStaged.check cell493 = true := by
  decide +kernel
theorem bound493 {x y : ℝ} (h : cell493.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell493 check493 h
def cell492 : Cell := gridCell 64 7 24
theorem check492 : PinnStaged.check cell492 = true := by
  decide +kernel
theorem bound492 {x y : ℝ} (h : cell492.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell492 check492 h
def cell491 : Cell := gridCell 64 7 25
theorem check491 : PinnStaged.check cell491 = true := by
  decide +kernel
theorem bound491 {x y : ℝ} (h : cell491.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell491 check491 h
def RawShard0090Cells : List Cell := [cell494, cell493, cell492, cell491]
theorem RawShard0090Valid : ValidCells RawShard0090Cells := by
  intro c hc x y h
  simp only [RawShard0090Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h494 | h493 | h492 | h491
  · subst c
    exact bound494 h
  · subst c
    exact bound493 h
  · subst c
    exact bound492 h
  · subst c
    exact bound491 h
#print axioms RawShard0090Valid
end PinnCertFarm
