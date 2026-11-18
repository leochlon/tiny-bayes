import FrozenExpr
import ExprNormalize

namespace PinnCert

/-- Semantically proved normalization of the unchanged frozen residual. -/
def normalizedResidual : Expr := residual.normalize
def residualDx : Expr := normalizedResidual.ndiff false
def residualDy : Expr := normalizedResidual.ndiff true
def residualNumerator : ℤ := 4831208875216605

theorem normalizedResidual_eq (x y : ℝ) : normalizedResidual.eval x y =
    -PoissonR3.Lap (fun a b => PoissonR3.N a b-PoissonR3.C a b) x y-PoissonR3.forcing x y := by
  rw [normalizedResidual,Expr.normalize_sound,residual_eq]

theorem residualNumerator_eq : (residualNumerator:ℝ)/S = PoissonR3.certR := by
  norm_num [residualNumerator,S,PoissonR3.certR]

#check normalizedResidual_eq
#print axioms normalizedResidual_eq
end PinnCert
