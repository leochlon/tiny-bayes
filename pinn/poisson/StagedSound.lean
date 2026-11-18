import StagedBindings
import StagedNumeric
namespace PinnStaged
open PinnCert

theorem interval_of_expr_eq {e f : Expr} (he : e = f) {x y : ℝ} {X Y : Iv}
    (hx : memAt S x X) (hy : memAt S y Y) : memAt S (f.eval x y) (e.interval X Y) := by
  have h := e.interval_sound hx hy
  rw [show e.eval x y = f.eval x y from congrArg (fun q : Expr => q.eval x y) he] at h
  exact h

theorem check_sound (b : Cell) (h : check b = true) {x y : ℝ} (hb : b.Contains x y) :
    |-PoissonR3.Lap (fun a b => PoissonR3.N a b-PoissonR3.C a b) x y
      -PoissonR3.forcing x y| ≤ PoissonR3.certR := by
  rw [← normalizedResidual_eq,← residualNumerator_eq]
  exact Cell.secondEnvelope_sound normalizedResidual b residualNumerator
    _ _ _ _ _ _ _
    (interval_of_expr_eq binding0 (Cell.memCst b.cx) (Cell.memCst b.cy))
    (interval_of_expr_eq binding1 (Cell.memCst b.cx) (Cell.memCst b.cy))
    (interval_of_expr_eq binding2 (Cell.memCst b.cx) (Cell.memCst b.cy))
    (fun u w hw => interval_of_expr_eq binding3 (b.memX ⟨hw.1,hw.2.1⟩) (b.memY ⟨hw.2.2.1,hw.2.2.2⟩))
    (fun u w hw => interval_of_expr_eq binding4 (b.memX ⟨hw.1,hw.2.1⟩) (b.memY ⟨hw.2.2.1,hw.2.2.2⟩))
    (fun u w hw => interval_of_expr_eq binding5 (b.memX ⟨hw.1,hw.2.1⟩) (b.memY ⟨hw.2.2.1,hw.2.2.2⟩))
    (fun u w hw => interval_of_expr_eq binding6 (b.memX ⟨hw.1,hw.2.1⟩) (b.memY ⟨hw.2.2.1,hw.2.2.2⟩))
    h hb

#check check_sound
#print axioms check_sound
end PinnStaged
