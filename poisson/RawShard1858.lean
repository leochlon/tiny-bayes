import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell6318 : Cell := gridCell 128 102 87
theorem check6318 : PinnStaged.check cell6318 = true := by
  decide +kernel
theorem bound6318 {x y : ℝ} (h : cell6318.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6318 check6318 h
def cell6317 : Cell := gridCell 128 103 86
theorem check6317 : PinnStaged.check cell6317 = true := by
  decide +kernel
theorem bound6317 {x y : ℝ} (h : cell6317.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6317 check6317 h
def cell6316 : Cell := gridCell 128 103 87
theorem check6316 : PinnStaged.check cell6316 = true := by
  decide +kernel
theorem bound6316 {x y : ℝ} (h : cell6316.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6316 check6316 h
def cell6443 : Cell := gridCell 128 96 88
theorem check6443 : PinnStaged.check cell6443 = true := by
  decide +kernel
theorem bound6443 {x y : ℝ} (h : cell6443.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell6443 check6443 h
def RawShard1858Cells : List Cell := [cell6318, cell6317, cell6316, cell6443]
theorem RawShard1858Valid : ValidCells RawShard1858Cells := by
  intro c hc x y h
  simp only [RawShard1858Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h6318 | h6317 | h6316 | h6443
  · subst c
    exact bound6318 h
  · subst c
    exact bound6317 h
  · subst c
    exact bound6316 h
  · subst c
    exact bound6443 h
#print axioms RawShard1858Valid
end PinnCertFarm
