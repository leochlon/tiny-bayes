import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6322 : Cell := gridCell 128 102 85
theorem check6322 : PinnStaged.check cell6322 = true := by
  decide +kernel
theorem bound6322 {x y : ℝ} (h : cell6322.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6322 check6322 h
def cell6321 : Cell := gridCell 128 103 84
theorem check6321 : PinnStaged.check cell6321 = true := by
  decide +kernel
theorem bound6321 {x y : ℝ} (h : cell6321.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6321 check6321 h
def cell6320 : Cell := gridCell 128 103 85
theorem check6320 : PinnStaged.check cell6320 = true := by
  decide +kernel
theorem bound6320 {x y : ℝ} (h : cell6320.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6320 check6320 h
def cell6319 : Cell := gridCell 128 102 86
theorem check6319 : PinnStaged.check cell6319 = true := by
  decide +kernel
theorem bound6319 {x y : ℝ} (h : cell6319.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6319 check6319 h
def RawShard1857Cells : List Cell := [cell6322, cell6321, cell6320, cell6319]
theorem RawShard1857Valid : ValidCells RawShard1857Cells := by
  intro c hc x y h
  simp only [RawShard1857Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6322 | h6321 | h6320 | h6319
  · subst c
    exact bound6322 h
  · subst c
    exact bound6321 h
  · subst c
    exact bound6320 h
  · subst c
    exact bound6319 h
#print axioms RawShard1857Valid
end PinnCertFarm
