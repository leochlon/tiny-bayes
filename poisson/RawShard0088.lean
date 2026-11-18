import FarmSemantics
import StagedSound
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def cell502 : Cell := gridCell 64 4 24
theorem check502 : PinnStaged.check cell502 = true := by
  decide +kernel
theorem bound502 {x y : ℝ} (h : cell502.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell502 check502 h
def cell501 : Cell := gridCell 64 4 25
theorem check501 : PinnStaged.check cell501 = true := by
  decide +kernel
theorem bound501 {x y : ℝ} (h : cell501.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell501 check501 h
def cell500 : Cell := gridCell 64 5 24
theorem check500 : PinnStaged.check cell500 = true := by
  decide +kernel
theorem bound500 {x y : ℝ} (h : cell500.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell500 check500 h
def cell499 : Cell := gridCell 64 5 25
theorem check499 : PinnStaged.check cell499 = true := by
  decide +kernel
theorem bound499 {x y : ℝ} (h : cell499.Contains x y) : ResidualBound x y := by
  unfold ResidualBound
  exact PinnStaged.check_sound cell499 check499 h
def RawShard0088Cells : List Cell := [cell502, cell501, cell500, cell499]
theorem RawShard0088Valid : ValidCells RawShard0088Cells := by
  intro c hc x y h
  simp only [RawShard0088Cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h502 | h501 | h500 | h499
  · subst c
    exact bound502 h
  · subst c
    exact bound501 h
  · subst c
    exact bound500 h
  · subst c
    exact bound499 h
#print axioms RawShard0088Valid
end PinnCertFarm
