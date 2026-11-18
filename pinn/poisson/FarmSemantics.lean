import HardCellData
import CellSecond
import ExactCover
namespace PinnCertFarm
open PinnCert
def ResidualBound (x y : ℝ) : Prop :=
  |-PoissonR3.Lap (fun a b => PoissonR3.N a b-PoissonR3.C a b) x y
    -PoissonR3.forcing x y| ≤ PoissonR3.certR
def ValidCells (cs : List Cell) : Prop :=
  ∀ c ∈ cs, ∀ x y, c.Contains x y → ResidualBound x y
theorem valid_append {cs ds : List Cell} (hc : ValidCells cs) (hd : ValidCells ds) :
    ValidCells (cs ++ ds) := by
  intro c h x y hxy
  rcases List.mem_append.mp h with h|h
  · exact hc c h x y hxy
  · exact hd c h x y hxy
end PinnCertFarm
