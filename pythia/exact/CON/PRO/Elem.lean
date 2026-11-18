import Mathlib
import CON.PRO.IntervalSound

/-! # Square root and rotary angles in interval arithmetic

`sqrtI` encloses `Real.sqrt`, and `cosI m f`, `sinI m f` enclose `cos (m / 10^f)`, `sin (m / 10^f)`,
all at scale `S`, by kernel-evaluable integer arithmetic (structural recursion only), each proved
sound over `ℝ`.

The kernel evaluates by name, so the iterations pass every intermediate value through
`Elem.forceNat` / `Elem.forceInt` / `Elem.forceIv`: these are the identity (`forceNat_eq`, ...),
but make the kernel compute the value once, before it is used. -/

namespace CON.PRO

universe u

namespace Elem

/-- `k n`, with `n` evaluated first. -/
def forceNat {α : Sort u} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem forceNat_eq {α : Sort u} (n : Nat) (k : Nat → α) : forceNat n k = k n := by
  cases n <;> rfl

/-- `k z`, with `z` evaluated first. -/
def forceInt {α : Sort u} (z : Int) (k : Int → α) : α :=
  match z with
  | Int.ofNat n => forceNat n fun n' => k (Int.ofNat n')
  | Int.negSucc n => forceNat n fun n' => k (Int.negSucc n')

theorem forceInt_eq {α : Sort u} (z : Int) (k : Int → α) : forceInt z k = k z := by
  cases z <;> simp only [forceInt, forceNat_eq]

/-- `k X`, with the three fields of `X` evaluated first. -/
def forceIv {α : Sort u} (X : Iv) (k : Iv → α) : α :=
  forceInt X.lo fun lo => forceInt X.hi fun hi =>
    match X.ok with
    | true => k ⟨lo, hi, true⟩
    | false => k ⟨lo, hi, false⟩

theorem forceIv_eq {α : Sort u} (X : Iv) (k : Iv → α) : forceIv X k = k X := by
  obtain ⟨lo, hi, ok⟩ := X
  cases ok <;> simp only [forceIv, forceInt_eq]

/-- `k P.1 P.2`, with the pair evaluated first. -/
def forcePair {α : Sort u} (P : Iv × Iv) (k : Iv → Iv → α) : α :=
  match P with
  | (a, b) => k a b

theorem forcePair_eq {α : Sort u} (P : Iv × Iv) (k : Iv → Iv → α) : forcePair P k = k P.1 P.2 := by
  obtain ⟨a, b⟩ := P
  rfl

/-! ## Square root -/

/-- Binary search for the bit length: for `n < 2^1024` the result `e` has `n < 2^(e+1)`. -/
def bitLenAux (n : Nat) : List Nat → Nat → Nat
  | [], e => e
  | b :: bs, e => forceNat (if n >>> (e + b) = 0 then e else e + b) fun e' => bitLenAux n bs e'

def bitLen (n : Nat) : Nat := bitLenAux n [512, 256, 128, 64, 32, 16, 8, 4, 2, 1] 0

/-- Newton iteration `g ↦ ⌊(g + ⌊n / g⌋) / 2⌋`. -/
def sqrtIter : Nat → Nat → Nat → Nat
  | 0, _, g => g
  | k + 1, n, g => forceNat ((g + n / g) / 2) fun g' => sqrtIter k n g'

/-- A candidate for `⌊√n⌋`; `sqrtFin` checks what is used of it. -/
def isqrt (n : Nat) : Nat := sqrtIter 16 n (2 ^ (bitLen n / 2 + 1))

/-- The enclosure `[a, b]` of the square root of `X`, valid when the four checks in `ok` hold. -/
def sqrtFin (X : Iv) (a b : Int) : Iv :=
  ⟨a, b, X.ok && decide (0 ≤ X.lo) && decide (0 ≤ a) && decide (0 ≤ b) && decide (a * a ≤ X.lo * S) &&
    decide (X.hi * S ≤ b * b)⟩

theorem memAt_sqrtFin {x : ℝ} {X : Iv} (hx : memAt S x X) (a b : ℤ) :
    memAt S (Real.sqrt x) (sqrtFin X a b) := by
  intro h
  simp only [sqrtFin, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hok, hlo0⟩, ha0⟩, hb0⟩, ha⟩, hb⟩ := h
  obtain ⟨h1, h2⟩ := hx hok
  have hS := S_pos
  have hlo0' : (0 : ℝ) ≤ X.lo := by exact_mod_cast hlo0
  have hxS : 0 ≤ x * S := le_trans hlo0' h1
  have hx0 : 0 ≤ x := by
    by_contra hc
    push_neg at hc
    exact absurd hxS (not_le.mpr (mul_neg_of_neg_of_pos hc hS))
  have ha0' : (0 : ℝ) ≤ a := by exact_mod_cast ha0
  have hb0' : (0 : ℝ) ≤ b := by exact_mod_cast hb0
  have ha' : (a : ℝ) * a ≤ X.lo * S := by exact_mod_cast ha
  have hb' : (X.hi : ℝ) * S ≤ b * b := by exact_mod_cast hb
  have hy0 : 0 ≤ Real.sqrt x * S := mul_nonneg (Real.sqrt_nonneg x) hS.le
  have hyy : Real.sqrt x * S * (Real.sqrt x * S) = x * S * S := by
    have h3 := Real.mul_self_sqrt hx0
    calc Real.sqrt x * S * (Real.sqrt x * S) = (Real.sqrt x * Real.sqrt x) * S * S := by ring
      _ = x * S * S := by rw [h3]
  have h3 : (X.lo : ℝ) * S ≤ x * S * S := mul_le_mul_of_nonneg_right h1 hS.le
  have h4 : x * S * S ≤ (X.hi : ℝ) * S := mul_le_mul_of_nonneg_right h2 hS.le
  simp only [sqrtFin]
  constructor
  · by_contra hc
    push_neg at hc
    have h5 := mul_self_lt_mul_self hy0 hc
    linarith
  · by_contra hc
    push_neg at hc
    have h5 := mul_self_lt_mul_self hb0' hc
    linarith

/-! ## Rotary angles -/

/-- Working scale `2^520` of the angle doubling. -/
def TT : Int :=
  3432398830065304857490950399540696608634717650071652704697231729592771591698828026061279820330727277488648155695740429018560993999858321906287014145557528576

/-- `TT / S = 2^220`. -/
def DD : Int := 1684996666696914987166688442938726917102321526408785780068975640576

/-- Number of doublings. -/
def KK : Nat := 180

/-- `TT / 2^KK = 2^340`. -/
def QQ : Int := 2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776

theorem TT_pos_int : (0 : ℤ) < TT := by decide

theorem DD_pos_int : (0 : ℤ) < DD := by decide

theorem TT_eq : TT = S * DD := by decide

theorem TT_pos : (0 : ℝ) < TT := by exact_mod_cast TT_pos_int

theorem TT_cast : (TT : ℝ) = (S : ℝ) * (DD : ℝ) := by exact_mod_cast TT_eq

theorem TT_real : (TT : ℝ) = QQ * 2 ^ KK := by norm_num [TT, QQ, KK]

/-- The same integers enclose `x'` at scale `s'` when `x' s' = x s`. -/
theorem memAt_rescale {s s' x x' : ℝ} {X : Iv} (h : x' * s' = x * s) (hx : memAt s x X) :
    memAt s' x' X := by
  intro hok
  rw [h]
  exact hx hok

/-- `1` at scale `TT`. -/
def oneT : Iv := ⟨TT, TT, true⟩

theorem memAt_oneT : memAt (TT : ℝ) 1 oneT := by
  intro _
  simp [oneT]

/-- One angle doubling at scale `TT`: `(cos a, sin a) ↦ (cos² a - sin² a, 2 sin a cos a)`. -/
def dbl (C Sn : Iv) : Iv × Iv :=
  (add (downBy TT (mulRaw C C)) (neg (downBy TT (mulRaw Sn Sn))), mulZ 2 (downBy TT (mulRaw Sn C)))

theorem memAt_dbl {a : ℝ} {C Sn : Iv} (hc : memAt (TT : ℝ) (Real.cos a) C)
    (hs : memAt (TT : ℝ) (Real.sin a) Sn) :
    memAt (TT : ℝ) (Real.cos (2 * a)) (dbl C Sn).1 ∧ memAt (TT : ℝ) (Real.sin (2 * a)) (dbl C Sn).2 := by
  constructor
  · have h3 := memAt_add (memAt_downBy TT_pos_int (memAt_mulRaw hc hc))
      (memAt_neg (memAt_downBy TT_pos_int (memAt_mulRaw hs hs)))
    have e : Real.cos (2 * a) = Real.cos a * Real.cos a + -(Real.sin a * Real.sin a) := by
      rw [Real.cos_two_mul']
      ring
    rw [e]
    exact h3
  · have h1 := memAt_mulZ 2 (memAt_downBy TT_pos_int (memAt_mulRaw hs hc))
    have e : Real.sin (2 * a) = ((2 : ℤ) : ℝ) * (Real.sin a * Real.cos a) := by
      rw [Real.sin_two_mul]
      push_cast
      ring
    rw [e]
    exact h1

/-- `k` doublings; every intermediate enclosure is evaluated before the next step. -/
def dblIter : Nat → Iv → Iv → Iv × Iv
  | 0, C, Sn => (C, Sn)
  | k + 1, C, Sn => forceIv (dbl C Sn).1 fun C' => forceIv (dbl C Sn).2 fun S' => dblIter k C' S'

theorem memAt_dblIter : ∀ (k : ℕ) (a : ℝ) (C Sn : Iv), memAt (TT : ℝ) (Real.cos a) C →
    memAt (TT : ℝ) (Real.sin a) Sn →
    memAt (TT : ℝ) (Real.cos (2 ^ k * a)) (dblIter k C Sn).1 ∧
      memAt (TT : ℝ) (Real.sin (2 ^ k * a)) (dblIter k C Sn).2
  | 0, a, C, Sn, hc, hs => by simpa [dblIter] using And.intro hc hs
  | k + 1, a, C, Sn, hc, hs => by
    obtain ⟨h1, h2⟩ := memAt_dbl hc hs
    have h3 := memAt_dblIter k (2 * a) _ _ h1 h2
    simp only [dblIter, forceIv_eq]
    rwa [show (2 : ℝ) ^ (k + 1) * a = 2 ^ k * (2 * a) by ring]

/-- The angle `m / 10^f / 2^KK` at scale `TT`. -/
def angI (m f : Nat) : Iv :=
  ⟨fdiv ((m : Int) * QQ) ((10 : Int) ^ f), cdiv ((m : Int) * QQ) ((10 : Int) ^ f), true⟩

theorem memAt_ang (m f : ℕ) : memAt (TT : ℝ) ((m : ℝ) / (10 : ℝ) ^ f / 2 ^ KK) (angI m f) := by
  intro _
  have hp : (0 : ℤ) < (10 : ℤ) ^ f := by positivity
  have hp' : (0 : ℝ) < (10 : ℝ) ^ f := by positivity
  have f1 := fdiv_mul_le ((m : ℤ) * QQ) ((10 : ℤ) ^ f) hp
  have f2 := le_cdiv_mul ((m : ℤ) * QQ) ((10 : ℤ) ^ f) hp
  push_cast at f1 f2
  have e : (m : ℝ) / (10 : ℝ) ^ f / 2 ^ KK * (TT : ℝ) = (m : ℝ) * QQ / (10 : ℝ) ^ f := by
    rw [TT_real]
    field_simp
  simp only [angI]
  rw [e]
  constructor
  · rw [le_div_iff₀ hp']
    exact f1
  · rw [div_le_iff₀ hp']
    exact f2

/-- `cos y ∈ [1 - y²/2, 1]`. -/
def cos0 (Y : Iv) : Iv :=
  ⟨(add oneT (neg (downBy 2 (downBy TT (mulRaw Y Y))))).lo, TT, Y.ok⟩

theorem memAt_cos0 {y : ℝ} {Y : Iv} (hy : memAt (TT : ℝ) y Y) :
    memAt (TT : ℝ) (Real.cos y) (cos0 Y) := by
  intro hok
  have hok' : Y.ok = true := hok
  have hT := TT_pos
  have h2 := memAt_downBy TT_pos_int (memAt_mulRaw hy hy)
  have h2' : memAt ((TT : ℝ) * ((2 : ℤ) : ℝ)) (y * y / 2) (downBy TT (mulRaw Y Y)) :=
    memAt_rescale (by push_cast; ring) h2
  have h3 := memAt_add memAt_oneT (memAt_neg (memAt_downBy (by norm_num) h2'))
  have hk : (add oneT (neg (downBy 2 (downBy TT (mulRaw Y Y))))).ok = true := by
    simp [add, neg, downBy, mulRaw, oneT, hok']
  obtain ⟨l, -⟩ := h3 hk
  have hc : 1 + -(y * y / 2) ≤ Real.cos y := by
    have h := Real.one_sub_sq_div_two_le_cos (x := y)
    rw [sq] at h
    linarith
  simp only [cos0]
  constructor
  · calc ((add oneT (neg (downBy 2 (downBy TT (mulRaw Y Y))))).lo : ℝ) ≤ (1 + -(y * y / 2)) * TT := l
      _ ≤ Real.cos y * TT := mul_le_mul_of_nonneg_right hc hT.le
  · calc Real.cos y * TT ≤ 1 * TT := mul_le_mul_of_nonneg_right (Real.cos_le_one y) hT.le
      _ = TT := one_mul _

/-- `sin y ∈ [y - y³/4, y]` for `0 ≤ y ≤ 1`. -/
def sin0 (Y : Iv) : Iv :=
  ⟨(add Y (neg (downBy 4 (downBy TT (mulRaw (downBy TT (mulRaw Y Y)) Y))))).lo, Y.hi,
    Y.ok && decide (0 ≤ Y.lo) && decide (Y.hi ≤ TT)⟩

theorem memAt_sin0 {y : ℝ} {Y : Iv} (hy : memAt (TT : ℝ) y Y) :
    memAt (TT : ℝ) (Real.sin y) (sin0 Y) := by
  intro hok
  simp only [sin0, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hok', hlo⟩, hhi⟩ := hok
  have hT := TT_pos
  obtain ⟨y1, y2⟩ := hy hok'
  have hlo' : (0 : ℝ) ≤ Y.lo := by exact_mod_cast hlo
  have hhi' : (Y.hi : ℝ) ≤ TT := by exact_mod_cast hhi
  have hy0 : 0 ≤ y := by
    by_contra hc
    push_neg at hc
    exact absurd (le_trans hlo' y1) (not_le.mpr (mul_neg_of_neg_of_pos hc hT))
  have hy1 : y ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h5 : 1 * (TT : ℝ) < y * TT := mul_lt_mul_of_pos_right hc hT
    linarith
  have h2 := memAt_downBy TT_pos_int (memAt_mulRaw hy hy)
  have h3 := memAt_downBy TT_pos_int (memAt_mulRaw h2 hy)
  have h3' : memAt ((TT : ℝ) * ((4 : ℤ) : ℝ)) (y * y * y / 4)
      (downBy TT (mulRaw (downBy TT (mulRaw Y Y)) Y)) :=
    memAt_rescale (by push_cast; ring) h3
  have h4 := memAt_add hy (memAt_neg (memAt_downBy (by norm_num) h3'))
  have hk : (add Y (neg (downBy 4 (downBy TT (mulRaw (downBy TT (mulRaw Y Y)) Y))))).ok = true := by
    simp [add, neg, downBy, mulRaw, hok']
  obtain ⟨l, -⟩ := h4 hk
  have hs : y + -(y * y * y / 4) ≤ Real.sin y := by
    rcases eq_or_lt_of_le hy0 with h0 | h0
    · rw [← h0]
      simp
    · have h := (Real.sin_gt_sub_cube h0 hy1).le
      have e : y ^ 3 = y * y * y := by ring
      rw [e] at h
      linarith
  simp only [sin0]
  constructor
  · calc ((add Y (neg (downBy 4 (downBy TT (mulRaw (downBy TT (mulRaw Y Y)) Y))))).lo : ℝ)
        ≤ (y + -(y * y * y / 4)) * TT := l
      _ ≤ Real.sin y * TT := mul_le_mul_of_nonneg_right hs hT.le
  · calc Real.sin y * TT ≤ y * TT := mul_le_mul_of_nonneg_right (Real.sin_le hy0) hT.le
      _ ≤ Y.hi := y2

end Elem

/-- Square root of a nonnegative interval at scale `S`: `[⌊√(lo S)⌋, ⌈√(hi S)⌉]`;
`ok = false` (no information) if `lo < 0`. -/
def sqrtI (X : Iv) : Iv :=
  Elem.forceIv X fun X =>
  Elem.forceNat (X.lo * S).toNat fun nlo =>
  Elem.forceNat (X.hi * S).toNat fun nhi =>
  Elem.forceNat (Elem.isqrt nlo) fun r =>
  Elem.forceNat (Elem.isqrt nhi) fun u =>
  Elem.forceNat (if r * r ≤ nlo then r else r - 1) fun a =>
  Elem.forceNat (if nhi ≤ u * u then u else u + 1) fun b =>
  Elem.forceIv (Elem.sqrtFin X (Int.ofNat a) (Int.ofNat b)) fun R => R

theorem memAt_sqrt {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S (Real.sqrt x) (sqrtI X) := by
  simp only [sqrtI, Elem.forceNat_eq, Elem.forceIv_eq]
  exact Elem.memAt_sqrtFin hx _ _

/-- Enclosures at scale `S` of `(cos (m / 10^f), sin (m / 10^f))`: elementary bounds at the angle
divided by `2^180`, then 180 angle doublings at scale `2^520`, then rounding outward to `S`.
`ok = false` (no information) if `m / 10^f > 2^180`. -/
def trigI (m f : Nat) : Iv × Iv :=
  Elem.forceNat m fun m =>
  Elem.forceNat f fun f =>
  Elem.forceIv (Elem.angI m f) fun Y =>
  Elem.forceIv (Elem.cos0 Y) fun C0 =>
  Elem.forceIv (Elem.sin0 Y) fun S0 =>
  Elem.forcePair (Elem.dblIter Elem.KK C0 S0) fun C Sn =>
  Elem.forceIv (downBy Elem.DD C) fun C' =>
  Elem.forceIv (downBy Elem.DD Sn) fun S' => (C', S')

/-- Enclosure of `cos (m / 10^f)` at scale `S`. -/
def cosI (m f : Nat) : Iv := (trigI m f).1

/-- Enclosure of `sin (m / 10^f)` at scale `S`. -/
def sinI (m f : Nat) : Iv := (trigI m f).2

theorem memAt_trig (m f : ℕ) :
    memAt S (Real.cos ((m : ℝ) / (10 : ℝ) ^ f)) (trigI m f).1 ∧
      memAt S (Real.sin ((m : ℝ) / (10 : ℝ) ^ f)) (trigI m f).2 := by
  have hy := Elem.memAt_ang m f
  obtain ⟨hc, hs⟩ := Elem.memAt_dblIter Elem.KK _ _ _ (Elem.memAt_cos0 hy) (Elem.memAt_sin0 hy)
  have e : (2 : ℝ) ^ Elem.KK * ((m : ℝ) / (10 : ℝ) ^ f / 2 ^ Elem.KK) = (m : ℝ) / (10 : ℝ) ^ f := by
    field_simp
  rw [e, Elem.TT_cast] at hc hs
  simp only [trigI, Elem.forceNat_eq, Elem.forceIv_eq, Elem.forcePair_eq]
  exact ⟨memAt_downBy Elem.DD_pos_int hc, memAt_downBy Elem.DD_pos_int hs⟩

theorem memAt_cos (m f : ℕ) : memAt S (Real.cos ((m : ℝ) / (10 : ℝ) ^ f)) (cosI m f) :=
  (memAt_trig m f).1

theorem memAt_sin (m f : ℕ) : memAt S (Real.sin ((m : ℝ) / (10 : ℝ) ^ f)) (sinI m f) :=
  (memAt_trig m f).2

end CON.PRO
