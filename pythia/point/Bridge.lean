import CON.Pythia
import PRO.Sound
import PRO.Checks

namespace PythiaCert

theorem f16num_eq (b : Nat) : CON.f16num b = PRO.f16num b := by
  by_cases h : (b / 32768) % 2 = 0
  · have h' : (b / 32768) % 2 ≠ 1 := by omega
    simp [CON.f16num, PRO.f16num, h, h']
  · have h' : (b / 32768) % 2 = 1 := by omega
    simp [CON.f16num, PRO.f16num, h, h']

theorem row_eq_vec (m r : Nat) : CON.row m r = PRO.vec r m := by
  unfold CON.row PRO.vec
  congr 1
  funext j
  norm_num [CON.f16, PRO.ent, CON.field, f16num_eq]

theorem row_length (m r : Nat) : (CON.row m r).length = m := by
  simp [CON.row]

theorem gelu_eq (x : ℝ) : CON.gelu x = PRO.gelu x := rfl

theorem layerNorm_eq (g b x : List ℝ) (hx : x.length = 128) :
    CON.layerNorm g b x = PRO.layerNorm g b x := by
  simp only [CON.layerNorm, PRO.layerNorm, PRO.lnMean, PRO.lnInvStd, hx,
    Nat.cast_ofNat, div_eq_mul_inv]
  rfl

theorem layerNorm_sound (g b : Nat) {x : List ℝ} {X : List PRO.Iv}
    (hxlen : x.length = 128) (hx : List.Forall₂ (PRO.memAt PRO.S) x X) :
    List.Forall₂ (PRO.memAt PRO.S)
      (CON.layerNorm (CON.row 128 g) (CON.row 128 b) x) (PRO.layerNormI g b X) := by
  rw [layerNorm_eq _ _ _ hxlen, row_eq_vec, row_eq_vec]
  exact PRO.f2_layerNorm g b hx

theorem row_sound (m r : Nat) :
    List.Forall₂ (PRO.memAt PRO.S) (CON.row m r) (PRO.vecI r m) := by
  rw [row_eq_vec]
  exact PRO.f2_vec r m

theorem f2_sub {x : List ℝ} {Xs : List PRO.Iv}
    (hx : List.Forall₂ (PRO.memAt PRO.S) x Xs) :
    ∀ Bs : List PRO.Iv, PRO.allSub Xs Bs = true → List.Forall₂ (PRO.memAt PRO.S) x Bs := by
  induction hx with
  | nil =>
    intro Bs h
    cases Bs with
    | nil => exact .nil
    | cons B Bs => simp [PRO.allSub] at h
  | cons hxa _ ih =>
    intro Bs h
    cases Bs with
    | nil => simp [PRO.allSub] at h
    | cons B Bs =>
      simp only [PRO.allSub, Bool.and_eq_true] at h
      exact .cons (PRO.memAt_inB hxa h.1) (ih Bs h.2)

#print axioms f16num_eq
#print axioms layerNorm_sound
#print axioms PRO.memAt_gelu

end PythiaCert
