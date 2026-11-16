import Mathlib
import CON.PRO.Act
import CON.PRO.IntervalSound
import CON.PRO.Pi

/-! # Interval enclosure of the exact GELU, proved sound

`geluI X` encloses `gelu x = x * Phi x` for every real `x` enclosed by `X` (`memAt_gelu`).

Mathematics. With `FF x = ∫_0^x exp (-t²/2) dt`, `tm n x = x^(2n+1) / (2n+1)!!` and
`KK N x = Σ_{n<N} tm n x`, for `x ≥ 0` and every `N`

    KK N x / exp (x²/2) ≤ FF x ≤ KK N x / exp (x²/2) + tm N x        (`F_bounds`)

because `FF - exp (-x²/2) * KK N` and `tm N - (FF - exp (-x²/2) * KK N)` vanish at `0` and have
nonnegative derivatives. `FF` is odd, so `Phi (-x) = 1 - Phi x`. The constant `1 / sqrt (2π)` is
enclosed from the enclosure of `π` in `PRO.Pi`.

Evaluation. All recursion is structural (on a fuel counter); intermediate intervals are forced to
literals (`forceIv`) so that the kernel evaluates every quantity once. -/

namespace CON.PRO

/-! ## Strict evaluation helpers -/

/-- `f m`, written so that kernel reduction evaluates `m` to a literal first. -/
def forceNat {α : Type} (m : Nat) (f : Nat → α) : α :=
  match m with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem forceNat_eq {α : Type} (m : Nat) (f : Nat → α) : forceNat m f = f m := by
  cases m <;> rfl

/-- `f z`, evaluating `z` first. -/
def forceInt {α : Type} (z : Int) (f : Int → α) : α :=
  match z with
  | Int.ofNat m => forceNat m fun m' => f (Int.ofNat m')
  | Int.negSucc m => forceNat m fun m' => f (Int.negSucc m')

theorem forceInt_eq {α : Type} (z : Int) (f : Int → α) : forceInt z f = f z := by
  cases z <;> simp [forceInt, forceNat_eq]

/-- `f X`, evaluating the three fields of `X` first. -/
def forceIv {α : Type} (X : Iv) (f : Iv → α) : α :=
  forceInt X.lo fun a => forceInt X.hi fun b =>
    match X.ok with
    | true => f ⟨a, b, true⟩
    | false => f ⟨a, b, false⟩

theorem forceIv_eq {α : Type} (X : Iv) (f : Iv → α) : forceIv X f = f X := by
  obtain ⟨a, b, c⟩ := X
  cases c <;> simp [forceIv, forceInt_eq]

/-! ## Interval operations for nonnegative quantities -/

/-- Product of two nonnegative intervals at scale `S` (two multiplications). -/
def mulP (X Y : Iv) : Iv :=
  ⟨fdiv (X.lo * Y.lo) S, cdiv (X.hi * Y.hi) S,
    X.ok && Y.ok && decide (0 ≤ X.lo) && decide (0 ≤ Y.lo)⟩

theorem memAt_mulP {x y : ℝ} {X Y : Iv} (hx : memAt S x X) (hy : memAt S y Y) :
    memAt S (x * y) (mulP X Y) := by
  intro h
  simp only [mulP, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hXok, hYok⟩, hX0⟩, hY0⟩ := h
  obtain ⟨x1, x2⟩ := hx hXok
  obtain ⟨y1, y2⟩ := hy hYok
  have hS := S_pos
  have hX0' : (0 : ℝ) ≤ X.lo := by exact_mod_cast hX0
  have hY0' : (0 : ℝ) ≤ Y.lo := by exact_mod_cast hY0
  have hxS : 0 ≤ x * S := le_trans hX0' x1
  have hyS : 0 ≤ y * S := le_trans hY0' y1
  have f1 := fdiv_mul_le (X.lo * Y.lo) S S_pos_int
  have f2 := le_cdiv_mul (X.hi * Y.hi) S S_pos_int
  push_cast at f1 f2
  have e : x * y * S * S = (x * S) * (y * S) := by ring
  simp only [mulP]
  constructor
  · apply le_of_mul_le_mul_right _ hS
    calc ((fdiv (X.lo * Y.lo) S : ℤ) : ℝ) * S ≤ X.lo * Y.lo := f1
      _ ≤ (x * S) * (y * S) := mul_le_mul x1 y1 hY0' hxS
      _ = x * y * S * S := e.symm
  · apply le_of_mul_le_mul_right _ hS
    calc x * y * S * S = (x * S) * (y * S) := e
      _ ≤ X.hi * Y.hi := mul_le_mul x2 y2 hyS (le_trans hxS x2)
      _ ≤ ((cdiv (X.hi * Y.hi) S : ℤ) : ℝ) * S := f2

/-- Division of the value by a positive integer. -/
theorem memAt_divN {s x : ℝ} {X : Iv} {d : ℤ} (hd : 0 < d) (hx : memAt s x X) :
    memAt s (x / d) (downBy d X) := by
  apply memAt_downBy hd
  intro h
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have := hx h
  rwa [show x / d * (s * d) = x * s by field_simp]

/-- Quotient of a nonnegative interval by a positive interval, at scale `S`. -/
def divP (K E : Iv) : Iv :=
  ⟨fdiv (K.lo * S) E.hi, cdiv (K.hi * S) E.lo,
    K.ok && E.ok && decide (0 ≤ K.lo) && decide (0 < E.lo)⟩

theorem memAt_divP {k e : ℝ} {K E : Iv} (hk : memAt S k K) (he : memAt S e E) :
    memAt S (k / e) (divP K E) := by
  intro h
  simp only [divP, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hKok, hEok⟩, hK0⟩, hE0⟩ := h
  obtain ⟨k1, k2⟩ := hk hKok
  obtain ⟨e1, e2⟩ := he hEok
  have hS := S_pos
  have hK0' : (0 : ℝ) ≤ K.lo := by exact_mod_cast hK0
  have hE0' : (0 : ℝ) < E.lo := by exact_mod_cast hE0
  have heS : 0 < e * S := lt_of_lt_of_le hE0' e1
  have he0 : 0 < e := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hEhi : (0 : ℝ) < E.hi := lt_of_lt_of_le heS e2
  have hEhi' : (0 : ℤ) < E.hi := by exact_mod_cast hEhi
  have hkS : 0 ≤ k * S := le_trans hK0' k1
  simp only [divP]
  constructor
  · have f1 := fdiv_mul_le (K.lo * S) E.hi hEhi'
    push_cast at f1
    have f0 : (0 : ℝ) ≤ ((fdiv (K.lo * S) E.hi : ℤ) : ℝ) := by
      exact_mod_cast fdiv_nonneg (mul_nonneg hK0 S_pos_int.le) hEhi'
    have step : ((fdiv (K.lo * S) E.hi : ℤ) : ℝ) * e * S ≤ k * S * S := by
      calc ((fdiv (K.lo * S) E.hi : ℤ) : ℝ) * e * S
          = ((fdiv (K.lo * S) E.hi : ℤ) : ℝ) * (e * S) := by ring
        _ ≤ ((fdiv (K.lo * S) E.hi : ℤ) : ℝ) * E.hi := mul_le_mul_of_nonneg_left e2 f0
        _ ≤ K.lo * S := f1
        _ ≤ k * S * S := mul_le_mul_of_nonneg_right k1 hS.le
    have step2 := le_of_mul_le_mul_right step hS
    rw [div_mul_eq_mul_div, le_div_iff₀ he0]
    exact step2
  · have f2 := le_cdiv_mul (K.hi * S) E.lo hE0
    push_cast at f2
    have c0 : (0 : ℝ) ≤ ((cdiv (K.hi * S) E.lo : ℤ) : ℝ) := by
      by_contra hc
      push_neg at hc
      have : (0 : ℝ) ≤ (K.hi : ℝ) * S := mul_nonneg (le_trans hkS k2) hS.le
      nlinarith
    have step : k * S * S ≤ ((cdiv (K.hi * S) E.lo : ℤ) : ℝ) * e * S := by
      calc k * S * S ≤ K.hi * S := mul_le_mul_of_nonneg_right k2 hS.le
        _ ≤ ((cdiv (K.hi * S) E.lo : ℤ) : ℝ) * E.lo := f2
        _ ≤ ((cdiv (K.hi * S) E.lo : ℤ) : ℝ) * (e * S) := mul_le_mul_of_nonneg_left e1 c0
        _ = ((cdiv (K.hi * S) E.lo : ℤ) : ℝ) * e * S := by ring
    have step2 := le_of_mul_le_mul_right step hS
    rw [div_mul_eq_mul_div, div_le_iff₀ he0]
    exact step2

/-- Smallest interval containing two intervals. -/
def hull (X Y : Iv) : Iv := ⟨min X.lo Y.lo, max X.hi Y.hi, X.ok && Y.ok⟩

theorem memAt_hull_left {s x : ℝ} {X Y : Iv} (h : memAt s x X) : memAt s x (hull X Y) := by
  intro hok
  simp only [hull, Bool.and_eq_true] at hok
  obtain ⟨h1, h2⟩ := h hok.1
  simp only [hull, Int.cast_min, Int.cast_max]
  exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_left _ _)⟩

theorem memAt_hull_right {s x : ℝ} {X Y : Iv} (h : memAt s x Y) : memAt s x (hull X Y) := by
  intro hok
  simp only [hull, Bool.and_eq_true] at hok
  obtain ⟨h1, h2⟩ := h hok.2
  simp only [hull, Int.cast_min, Int.cast_max]
  exact ⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_right _ _)⟩

/-! ## The series for `∫_0^x exp (-t²/2) dt` -/

noncomputable section

/-- `1 / (2n+1)!!`. -/
def ai : ℕ → ℝ
  | 0 => 1
  | n + 1 => ai n / (2 * (n : ℝ) + 3)

theorem ai_pos : ∀ n, 0 < ai n
  | 0 => by simp [ai]
  | n + 1 => by
    have h := ai_pos n
    simp only [ai]
    exact div_pos h (by positivity)

/-- `x^(2n+1) / (2n+1)!!`. -/
def tm (n : ℕ) (y : ℝ) : ℝ := ai n * y ^ (2 * n + 1)

/-- `Σ_{n<N} tm n`. -/
def KK : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, y => KK n y + tm n y

/-- The derivative of `KK N`. -/
def KK' : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, y => KK' n y + ai n * ((2 * (n : ℝ) + 1) * y ^ (2 * n))

/-- `∫_0^x exp (-t²/2) dt`. -/
def FF (x : ℝ) : ℝ :=
  intervalIntegral (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) 0 x MeasureTheory.volume

end

theorem tm_zero (n : ℕ) : tm n 0 = 0 := by
  have h : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
  simp [tm, h]

theorem KK_zero : ∀ N, KK N 0 = 0
  | 0 => rfl
  | n + 1 => by simp [KK, tm_zero, KK_zero n]

theorem FF_zero : FF 0 = 0 := by simp [FF]

theorem hasDerivAt_tm (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => tm n y) (ai n * ((2 * (n : ℝ) + 1) * y ^ (2 * n))) y := by
  have h := (hasDerivAt_pow (2 * n + 1) y).const_mul (ai n)
  simp only [Nat.add_sub_cancel] at h
  have e : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
  rw [e] at h
  exact h

theorem hasDerivAt_KK : ∀ (n : ℕ) (y : ℝ), HasDerivAt (fun y => KK n y) (KK' n y) y
  | 0, y => hasDerivAt_const y (0 : ℝ)
  | n + 1, y => (hasDerivAt_KK n y).add (hasDerivAt_tm n y)

theorem KK_ident : ∀ (n : ℕ) (y : ℝ),
    KK' n y - y * KK n y = 1 - (2 * (n : ℝ) + 1) * ai n * y ^ (2 * n)
  | 0, y => by simp [KK, KK', ai]
  | n + 1, y => by
    have ih := KK_ident n y
    have h : ai (n + 1) * (2 * (n : ℝ) + 3) = ai n := by
      have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      simp only [ai]
      field_simp
    simp only [KK, KK', tm]
    push_cast
    linear_combination ih + y ^ (2 * n + 2) * h

theorem hasDerivAt_FF (y : ℝ) : HasDerivAt (fun u => FF u) (Real.exp (-(y ^ 2) / 2)) y :=
  ((show Continuous fun t : ℝ => Real.exp (-(t ^ 2) / 2) by fun_prop).integral_hasStrictDerivAt
    0 y).hasDerivAt

theorem hasDerivAt_E (y : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) (Real.exp (-(y ^ 2) / 2) * (-y)) y := by
  have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-y) y := by
    have h := (hasDerivAt_pow 2 y).const_mul (-(1 : ℝ) / 2)
    have e : (fun u : ℝ => -(u ^ 2) / 2) = fun u : ℝ => -(1 : ℝ) / 2 * u ^ 2 := by
      funext u
      ring
    rw [e]
    convert h using 1
    norm_num
    ring
  exact h1.exp

theorem F_lower (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : Real.exp (-(x ^ 2) / 2) * KK N x ≤ FF x := by
  have hd : ∀ y, HasDerivAt (fun u => FF u - Real.exp (-(u ^ 2) / 2) * KK N u)
      (Real.exp (-(y ^ 2) / 2) * ((2 * (N : ℝ) + 1) * ai N * y ^ (2 * N))) y := by
    intro y
    have h := (hasDerivAt_FF y).sub ((hasDerivAt_E y).mul (hasDerivAt_KK N y))
    have e : Real.exp (-(y ^ 2) / 2) -
        (Real.exp (-(y ^ 2) / 2) * (-y) * KK N y + Real.exp (-(y ^ 2) / 2) * KK' N y) =
        Real.exp (-(y ^ 2) / 2) * ((2 * (N : ℝ) + 1) * ai N * y ^ (2 * N)) := by
      have hi := KK_ident N y
      linear_combination (-Real.exp (-(y ^ 2) / 2)) * hi
    rw [← e]
    exact h
  have hm : Monotone (fun u => FF u - Real.exp (-(u ^ 2) / 2) * KK N u) := by
    apply monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    intro y
    rw [(hd y).deriv]
    have h1 : 0 ≤ y ^ (2 * N) := by rw [pow_mul]; positivity
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (by positivity) (ai_pos N).le) h1)
  have h0 := hm hx
  simp only [FF_zero, KK_zero, mul_zero, sub_zero] at h0
  linarith

theorem F_upper (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    FF x ≤ Real.exp (-(x ^ 2) / 2) * KK N x + tm N x := by
  have hd : ∀ y, HasDerivAt (fun u => tm N u - (FF u - Real.exp (-(u ^ 2) / 2) * KK N u))
      ((1 - Real.exp (-(y ^ 2) / 2)) * (ai N * ((2 * (N : ℝ) + 1) * y ^ (2 * N)))) y := by
    intro y
    have h := (hasDerivAt_tm N y).sub
      ((hasDerivAt_FF y).sub ((hasDerivAt_E y).mul (hasDerivAt_KK N y)))
    have e : ai N * ((2 * (N : ℝ) + 1) * y ^ (2 * N)) - (Real.exp (-(y ^ 2) / 2) -
        (Real.exp (-(y ^ 2) / 2) * (-y) * KK N y + Real.exp (-(y ^ 2) / 2) * KK' N y)) =
        (1 - Real.exp (-(y ^ 2) / 2)) * (ai N * ((2 * (N : ℝ) + 1) * y ^ (2 * N))) := by
      have hi := KK_ident N y
      linear_combination (Real.exp (-(y ^ 2) / 2)) * hi
    rw [← e]
    exact h
  have hm : Monotone (fun u => tm N u - (FF u - Real.exp (-(u ^ 2) / 2) * KK N u)) := by
    apply monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    intro y
    rw [(hd y).deriv]
    have h1 : 0 ≤ y ^ (2 * N) := by rw [pow_mul]; positivity
    have h2 : Real.exp (-(y ^ 2) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := sq_nonneg y
      linarith
    exact mul_nonneg (sub_nonneg.mpr h2) (mul_nonneg (ai_pos N).le (mul_nonneg (by positivity) h1))
  have h0 := hm hx
  simp only [FF_zero, KK_zero, tm_zero, mul_zero, sub_zero] at h0
  linarith

/-- The series bounds, in the form used by the evaluator. -/
theorem F_bounds (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    KK N x / Real.exp (x ^ 2 / 2) ≤ FF x ∧ FF x ≤ KK N x / Real.exp (x ^ 2 / 2) + tm N x := by
  have e : Real.exp (-(x ^ 2) / 2) * KK N x = KK N x / Real.exp (x ^ 2 / 2) := by
    rw [neg_div, Real.exp_neg]
    ring
  rw [← e]
  exact ⟨F_lower N hx, F_upper N hx⟩

theorem FF_neg (x : ℝ) : FF (-x) = -FF x := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x)
    (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
  simp only [neg_sq, neg_zero] at h
  unfold FF
  rw [h, intervalIntegral.integral_symm (-x) 0]

theorem Phi_neg (x : ℝ) : Phi x = 1 - Phi (-x) := by
  have h := FF_neg x
  have e1 : Phi x = 1 / 2 + FF x / Real.sqrt (2 * Real.pi) := rfl
  have e2 : Phi (-x) = 1 / 2 + FF (-x) / Real.sqrt (2 * Real.pi) := rfl
  rw [e1, e2, h]
  ring

/-! ## The constants `1/2` and `1 / sqrt (2π)` -/

/-- `1/2` at scale `S`. -/
def halfI : Iv :=
  ⟨1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688,
    1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688, true⟩

theorem memAt_half : memAt S (1 / 2) halfI := by
  intro _
  norm_num [halfI, S]

/-- Enclosure of `1 / sqrt (2π)`, from the enclosure `piI` of `π`. -/
def invSqrt2PiI : Iv := recip (sqrtI (mulZ 2 piI))

theorem memAt_invSqrt2Pi : memAt S (Real.sqrt (2 * Real.pi))⁻¹ invSqrt2PiI := by
  have h := memAt_mulZ 2 memAt_pi
  have e : ((2 : ℤ) : ℝ) * Real.pi = 2 * Real.pi := by norm_num
  rw [e] at h
  exact memAt_recip (memAt_sqrt h)

/-! ## The evaluator -/

/-- Stop the series when the next term is at most `2^150 / S = 2^(-150)`. -/
def THRESH : Int := 1427247692705959881058285969449495136382746624

/-- From enclosures `Ep` of `exp (x²/2)`, `K` of `KK N x` and `T` of `tm N x`: an enclosure of `FF x`. -/
def finI (Ep K T : Iv) : Iv :=
  let G := divP K Ep
  ⟨G.lo, G.hi + T.hi, G.ok && T.ok⟩

theorem finI_sound {f k e t : ℝ} {Ep K T : Iv} (hlo : k / e ≤ f) (hhi : f ≤ k / e + t)
    (hG : memAt S (k / e) (divP K Ep)) (hT : memAt S t T) : memAt S f (finI Ep K T) := by
  intro h
  simp only [finI, Bool.and_eq_true] at h
  obtain ⟨g1, g2⟩ := hG h.1
  obtain ⟨t1, t2⟩ := hT h.2
  have hS := S_pos
  simp only [finI]
  constructor
  · calc ((divP K Ep).lo : ℝ) ≤ k / e * S := g1
      _ ≤ f * S := mul_le_mul_of_nonneg_right hlo hS.le
  · push_cast
    calc f * S ≤ (k / e + t) * S := mul_le_mul_of_nonneg_right hhi hS.le
      _ = k / e * S + t * S := by ring
      _ ≤ (divP K Ep).hi + T.hi := add_le_add g2 t2

/-- The series loop: `T` encloses `tm n x`, `K` encloses `KK n x`, `X2` encloses `x²`. -/
def serI : Nat → Nat → Iv → Iv → Iv → Iv → Iv
  | 0, _, _, Ep, T, K => finI Ep K T
  | fuel + 1, n, X2, Ep, T, K =>
    if T.hi ≤ THRESH then finI Ep K T
    else
      forceIv (downBy ((2 * n + 3 : Nat) : Int) (mulP T X2)) fun T' =>
        forceIv (add K T) fun K' => serI fuel (n + 1) X2 Ep T' K'

theorem tm_succ (n : ℕ) (x : ℝ) :
    tm (n + 1) x = tm n x * x ^ 2 / (((2 * n + 3 : ℕ) : ℤ) : ℝ) := by
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  simp only [tm, ai]
  push_cast
  rw [div_mul_eq_mul_div, div_left_inj' h3]
  ring

theorem serI_sound {x : ℝ} (hx : 0 ≤ x) {X2 Ep : Iv} (h2 : memAt S (x ^ 2) X2)
    (hE : memAt S (Real.exp (x ^ 2 / 2)) Ep) :
    ∀ (fuel n : ℕ) (T K : Iv), memAt S (tm n x) T → memAt S (KK n x) K →
      memAt S (FF x) (serI fuel n X2 Ep T K)
  | 0, n, T, K, hT, hK => by
    simp only [serI]
    exact finI_sound (F_bounds n hx).1 (F_bounds n hx).2 (memAt_divP hK hE) hT
  | fuel + 1, n, T, K, hT, hK => by
    simp only [serI]
    split_ifs with hstop
    · exact finI_sound (F_bounds n hx).1 (F_bounds n hx).2 (memAt_divP hK hE) hT
    · rw [forceIv_eq, forceIv_eq]
      apply serI_sound hx h2 hE fuel (n + 1)
      · rw [tm_succ]
        exact memAt_divN (by exact_mod_cast Nat.succ_pos _) (memAt_mulP hT h2)
      · exact memAt_add hK hT

/-- Fuel of the series loop (enough for `|x| ≤ 55` at the threshold `2^(-150)`). -/
def FUEL : Nat := 5000

/-- Enclosure of `Phi x` for `x ≥ 0`. -/
def phiPos (X : Iv) : Iv :=
  forceIv (mulP X X) fun X2 =>
    forceIv (expI (downBy 2 X2)) fun Ep =>
      forceIv (serI FUEL 0 X2 Ep X zero) fun FI =>
        add halfI (mul FI invSqrt2PiI)

theorem phiPos_sound {x : ℝ} {X : Iv} (hx : memAt S x X) (hx0 : 0 ≤ x) :
    memAt S (Phi x) (phiPos X) := by
  simp only [phiPos, forceIv_eq]
  have h2 : memAt S (x ^ 2) (mulP X X) := by
    rw [sq]
    exact memAt_mulP hx hx
  have hE : memAt S (Real.exp (x ^ 2 / 2)) (expI (downBy 2 (mulP X X))) := by
    have h := memAt_exp (memAt_divN (d := 2) (by norm_num) h2)
    have e : x ^ 2 / ((2 : ℤ) : ℝ) = x ^ 2 / 2 := by norm_num
    rw [e] at h
    exact h
  have hT : memAt S (tm 0 x) X := by
    have e : tm 0 x = x := by simp [tm, ai]
    rw [e]
    exact hx
  have hK : memAt S (KK 0 x) zero := memAt_zero S
  have hF := serI_sound hx0 h2 hE FUEL 0 X zero hT hK
  have e : Phi x = 1 / 2 + FF x * (Real.sqrt (2 * Real.pi))⁻¹ := by
    unfold Phi FF
    ring
  rw [e]
  exact memAt_add memAt_half (memAt_mul hF memAt_invSqrt2Pi)

/-- `gelu` on an interval of nonnegative numbers. -/
def geluPos (X : Iv) : Iv := mul X (phiPos X)

/-- `gelu` on an interval of nonpositive numbers, by `Phi x = 1 - Phi (-x)`. -/
def geluNeg (X : Iv) : Iv := mul X (add one (neg (phiPos (neg X))))

theorem mul_ok_left {X Y : Iv} (h : (mul X Y).ok = true) : X.ok = true := by
  simp only [mul, downBy, mulRaw, Bool.and_eq_true] at h
  exact h.1

theorem geluPos_sound {x : ℝ} {X : Iv} (hx : memAt S x X) (h0 : X.ok = true → 0 ≤ x) :
    memAt S (gelu x) (geluPos X) := by
  intro hok
  have hX := mul_ok_left hok
  exact memAt_mul hx (phiPos_sound hx (h0 hX)) hok

theorem geluNeg_sound {x : ℝ} {X : Iv} (hx : memAt S x X) (h0 : X.ok = true → x ≤ 0) :
    memAt S (gelu x) (geluNeg X) := by
  intro hok
  have hX := mul_ok_left hok
  have hx0 : 0 ≤ -x := by linarith [h0 hX]
  have hp := phiPos_sound (memAt_neg hx) hx0
  have e : gelu x = x * (1 + -Phi (-x)) := by
    unfold gelu
    rw [Phi_neg x]
    ring
  rw [e]
  exact memAt_mul hx (memAt_add memAt_one (memAt_neg hp)) hok

/-- `gelu` on an arbitrary interval. -/
def geluCore (X : Iv) : Iv :=
  if 0 ≤ X.lo then geluPos X
  else if X.hi ≤ 0 then geluNeg X
  else hull (geluPos ⟨0, X.hi, X.ok⟩) (geluNeg ⟨X.lo, 0, X.ok⟩)

theorem geluCore_sound {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S (gelu x) (geluCore X) := by
  have hS := S_pos
  unfold geluCore
  split_ifs with h1 h2
  · apply geluPos_sound hx
    intro hok
    have h := (hx hok).1
    have h1' : (0 : ℝ) ≤ X.lo := by exact_mod_cast h1
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos (neg_pos.mpr hc) hS]
  · apply geluNeg_sound hx
    intro hok
    have h := (hx hok).2
    have h2' : (X.hi : ℝ) ≤ 0 := by exact_mod_cast h2
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos hc hS]
  · rcases le_total 0 x with hx0 | hx0
    · apply memAt_hull_left
      apply geluPos_sound (X := ⟨0, X.hi, X.ok⟩)
      · intro hok
        exact ⟨by simpa using mul_nonneg hx0 hS.le, (hx hok).2⟩
      · intro _
        exact hx0
    · apply memAt_hull_right
      apply geluNeg_sound (X := ⟨X.lo, 0, X.ok⟩)
      · intro hok
        exact ⟨(hx hok).1, by simpa using mul_nonpos_of_nonpos_of_nonneg hx0 hS.le⟩
      · intro _
        exact hx0

/-- Interval enclosure of the exact GELU; input and output are forced to literals. -/
def geluI (X : Iv) : Iv := forceIv X fun X' => forceIv (geluCore X') fun R => R

/-- **Soundness of `geluI`.** -/
theorem memAt_gelu {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S (gelu x) (geluI X) := by
  simp only [geluI, forceIv_eq]
  exact geluCore_sound hx

end CON.PRO
