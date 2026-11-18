import Expr

namespace PinnCert

def ratI (q : ℚ) : Iv :=
  ⟨fdiv (q.num*S) q.den, cdiv (q.num*S) q.den, true⟩

theorem memAt_rat (q : ℚ) : memAt S (q:ℝ) (ratI q) := by
  have hd : (0:ℤ) < q.den := by exact_mod_cast q.pos
  have h := memAt_downBy (s := (S:ℝ)) hd
    (memAt_cst (q.num*S) (q:ℝ) ((S:ℝ)*q.den) (by
      rw [Rat.cast_def]
      push_cast
      field_simp
      <;> ring))
  exact h

namespace Expr
def interval : Expr → Iv → Iv → Iv
  | .rat q, _, _ => ratI q
  | .x, X, _ => X
  | .y, _, Y => Y
  | .add a b, X, Y => PinnCert.add (interval a X Y) (interval b X Y)
  | .neg a, X, Y => PinnCert.neg (interval a X Y)
  | .mul a b, X, Y => PinnCert.mul (interval a X Y) (interval b X Y)
  | .exp a, X, Y => expI (interval a X Y)
  | .tanh a, X, Y => tanhI (interval a X Y)

theorem interval_sound (e : Expr) {x y : ℝ} {X Y : Iv}
    (hx : memAt S x X) (hy : memAt S y Y) :
    memAt S (e.eval x y) (e.interval X Y) := by
  induction e with
  | rat q => exact memAt_rat q
  | x => exact hx
  | y => exact hy
  | add a b ha hb => exact memAt_add ha hb
  | neg a ha => exact memAt_neg ha
  | mul a b ha hb => exact memAt_mul ha hb
  | exp a ha => exact memAt_exp ha
  | tanh a ha => exact memAt_tanh ha

def boundCheck (e : Expr) (X Y : Iv) (r : ℚ) : Bool :=
  let I := e.interval X Y
  I.ok && decide ((-r*S:ℚ) ≤ I.lo) && decide ((I.hi:ℚ) ≤ r*S)

theorem boundCheck_sound (e : Expr) {x y : ℝ} {X Y : Iv} {r : ℚ}
    (hx : memAt S x X) (hy : memAt S y Y) (h : e.boundCheck X Y r = true) :
    |e.eval x y| ≤ (r:ℝ) := by
  simp only [boundCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl,hu⟩ := e.interval_sound hx hy h.1.1
  have hL : -(r:ℝ)*(S:ℝ) ≤ (e.interval X Y).lo := by exact_mod_cast h.1.2
  have hU : ((e.interval X Y).hi:ℝ) ≤ (r:ℝ)*(S:ℝ) := by exact_mod_cast h.2
  apply abs_le.mpr
  exact ⟨(mul_le_mul_iff_left₀ S_pos).mp (hL.trans hl),
    (mul_le_mul_iff_left₀ S_pos).mp (hu.trans hU)⟩

#check interval_sound
#check boundCheck_sound
#print axioms interval_sound
#print axioms boundCheck_sound
end Expr
end PinnCert
