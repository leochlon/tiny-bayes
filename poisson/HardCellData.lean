import ResidualData
import CellMVT

namespace PinnCert
def gridCell (n i j : ℤ) : Cell := ⟨i*S/n,(i+1)*S/n,j*S/n,(j+1)*S/n⟩
def hardCell : Cell := gridCell 256 120 255
def hardCellPart (i j : Fin 16) : Cell := gridCell 4096 (1920+i.val) (4080+j.val)

/-- Each row is checked independently in its own kernel module. -/
def hardRowCheck (i : Fin 16) : Prop :=
  ∀ j : Fin 16, Cell.firstCheck normalizedResidual (hardCellPart i j) residualNumerator = true

instance (i : Fin 16) : Decidable (hardRowCheck i) := inferInstanceAs (Decidable (∀ j : Fin 16,
  Cell.firstCheck normalizedResidual (hardCellPart i j) residualNumerator = true))

theorem hardPart_bound {i j : Fin 16} (h : hardRowCheck i) {x y : ℝ}
    (hb : (hardCellPart i j).Contains x y) :
    |(-PoissonR3.Lap (fun a b => PoissonR3.N a b-PoissonR3.C a b) x y)-PoissonR3.forcing x y|
      ≤ PoissonR3.certR := by
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.firstCheck_sound normalizedResidual (hardCellPart i j) residualNumerator (h j) hb

#print axioms hardPart_bound
end PinnCert
