import IntervalSound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace PinnCert

inductive Expr where
  | rat : ℚ → Expr
  | x : Expr
  | y : Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | exp : Expr → Expr
  | tanh : Expr → Expr
  deriving Repr, DecidableEq

namespace Expr
instance : Add Expr := ⟨Expr.add⟩
instance : Neg Expr := ⟨Expr.neg⟩
instance : Sub Expr := ⟨fun a b => a + -b⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance (n : ℕ) : OfNat Expr n := ⟨Expr.rat n⟩

noncomputable def eval : Expr → ℝ → ℝ → ℝ
  | .rat q, _, _ => q
  | .x, u, _ => u
  | .y, _, v => v
  | .add a b, u, v => eval a u v + eval b u v
  | .neg a, u, v => -eval a u v
  | .mul a b, u, v => eval a u v * eval b u v
  | .exp a, u, v => Real.exp (eval a u v)
  | .tanh a, u, v => Real.tanh (eval a u v)

@[simp] theorem eval_rat (q : ℚ) (x y : ℝ) : eval (.rat q) x y = q := rfl
@[simp] theorem eval_add (a b : Expr) (x y : ℝ) : eval (a+b) x y = eval a x y+eval b x y := rfl
@[simp] theorem eval_neg (a : Expr) (x y : ℝ) : eval (-a) x y = -eval a x y := rfl
@[simp] theorem eval_sub (a b : Expr) (x y : ℝ) : eval (a-b) x y = eval a x y-eval b x y := rfl
@[simp] theorem eval_mul (a b : Expr) (x y : ℝ) : eval (a*b) x y = eval a x y*eval b x y := rfl
@[simp] theorem eval_nat (n : ℕ) (x y : ℝ) : eval (OfNat.ofNat n) x y = n := by simp [OfNat.ofNat, eval]

def diff (axis : Bool) : Expr → Expr
  | .rat _ => 0
  | .x => if axis then 0 else 1
  | .y => if axis then 1 else 0
  | .add a b => diff axis a + diff axis b
  | .neg a => -diff axis a
  | .mul a b => diff axis a*b + a*diff axis b
  | .exp a => .exp a * diff axis a
  | .tanh a => (1 - .tanh a * .tanh a) * diff axis a

theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x) hc
  have e : (fun y => Real.sinh y / Real.cosh y) = Real.tanh := by
    funext y
    rw [Real.tanh_eq_sinh_div_cosh]
  rw [e] at h
  have e2 : 1 - Real.tanh x ^ 2 = (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [e2]
  exact h

theorem hasDerivAt_eval_x (e : Expr) (x y : ℝ) :
    HasDerivAt (fun t => e.eval t y) ((e.diff false).eval x y) x := by
  induction e with
  | rat q => simpa [diff, eval] using hasDerivAt_const x (q:ℝ)
  | x => simpa [diff, eval] using hasDerivAt_id x
  | y => simpa [diff, eval] using hasDerivAt_const x y
  | add a b ha hb => exact ha.add hb
  | neg a ha => exact ha.neg
  | mul a b ha hb => exact ha.mul hb
  | exp a ha => exact ha.exp
  | tanh a ha =>
    simpa [diff, eval, pow_two] using (hasDerivAt_tanh (a.eval x y)).comp x ha

theorem hasDerivAt_eval_y (e : Expr) (x y : ℝ) :
    HasDerivAt (fun t => e.eval x t) ((e.diff true).eval x y) y := by
  induction e with
  | rat q => simpa [diff, eval] using hasDerivAt_const y (q:ℝ)
  | x => simpa [diff, eval] using hasDerivAt_const y x
  | y => simpa [diff, eval] using hasDerivAt_id y
  | add a b ha hb => exact ha.add hb
  | neg a ha => exact ha.neg
  | mul a b ha hb => exact ha.mul hb
  | exp a ha => exact ha.exp
  | tanh a ha =>
    simpa [diff, eval, pow_two] using (hasDerivAt_tanh (a.eval x y)).comp y ha

theorem deriv_eval_x (e : Expr) (x y : ℝ) :
    deriv (fun t => e.eval t y) x = (e.diff false).eval x y :=
  (e.hasDerivAt_eval_x x y).deriv

theorem deriv_eval_y (e : Expr) (x y : ℝ) :
    deriv (fun t => e.eval x t) y = (e.diff true).eval x y :=
  (e.hasDerivAt_eval_y x y).deriv

theorem deriv2_eval_x (e : Expr) (x y : ℝ) :
    deriv (deriv (fun t => e.eval t y)) x = ((e.diff false).diff false).eval x y := by
  have h : deriv (fun t => e.eval t y) = fun t => (e.diff false).eval t y :=
    funext fun t => e.deriv_eval_x t y
  rw [h, deriv_eval_x]

theorem deriv2_eval_y (e : Expr) (x y : ℝ) :
    deriv (deriv (fun t => e.eval x t)) y = ((e.diff true).diff true).eval x y := by
  have h : deriv (fun t => e.eval x t) = fun t => (e.diff true).eval x t :=
    funext fun t => e.deriv_eval_y x t
  rw [h, deriv_eval_y]

#check hasDerivAt_eval_x
#check hasDerivAt_eval_y
#print axioms hasDerivAt_eval_x
#print axioms deriv2_eval_x
#print axioms deriv2_eval_y
end Expr
end PinnCert
