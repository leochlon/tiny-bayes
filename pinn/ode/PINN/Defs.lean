import PINN.Cert
import PINN.DataN
import PINN.DataH

/-! # Definitions used by `PINN.Main`, and the link from the kernel checks to them -/

namespace PINN

open Set

/-- `M` is continuously differentiable on `[0, 4]` (derivatives within `[0, 4]`). -/
def C1On (M : ℝ → ℝ) : Prop :=
  DifferentiableOn ℝ M (Icc 0 4) ∧ ContinuousOn (derivWithin M (Icc 0 4)) (Icc 0 4)

/-- Hypotheses of the residual-sum bound: the partition and the residual bounds. -/
def Bounds (M : ℝ → ℝ) (K : ℕ) (a lo hi : ℕ → ℝ) : Prop :=
  a 0 = 0 ∧ a K = 4 ∧ (∀ k < K, a k < a (k + 1)) ∧ (∀ k < K, lo k ≤ hi k) ∧
    ∀ k < K, ∀ s ∈ Icc (a k) (a (k + 1)),
      lo k ≤ derivWithin M (Icc 0 4) s + M s - Real.exp (-s) ∧
        derivWithin M (Icc 0 4) s + M s - Real.exp (-s) ≤ hi k

/-- Lower residual-sum bound: `e^{-t} (1 - M 0) - Σₖ hi_k w_k(t)`. -/
noncomputable def lowerB (M : ℝ → ℝ) (K : ℕ) (a hi : ℕ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t) * (1 - M 0) - ∑ k ∈ Finset.range K, hi k * wk a k t

/-- Upper residual-sum bound: `e^{-t} (1 - M 0) - Σₖ lo_k w_k(t)`. -/
noncomputable def upperB (M : ℝ → ℝ) (K : ℕ) (a lo : ℕ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t) * (1 - M 0) - ∑ k ∈ Finset.range K, lo k * wk a k t

/-- For any model, the residual-sum bounds within `ε` everywhere give `|u - M| ≤ ε`. -/
theorem residual_route_core (M : ℝ → ℝ) (hM : C1On M) (ε : ℝ) (K : ℕ) (a lo hi : ℕ → ℝ) (hb : Bounds M K a lo hi)
    (hε : ∀ t ∈ Icc (0 : ℝ) 4, -ε ≤ lowerB M K a hi t ∧ upperB M K a lo t ≤ ε)
    (u : ℝ → ℝ) (hu : IsSolution u) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) : |u t - M t| ≤ ε := by
  have h1 := residual_sum_bound M (derivWithin M (Icc 0 4)) (fun s hs => (hM.1 s hs).hasDerivWithinAt) hM.2 K a lo hi
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.2 u hu t ht
  have h2 := hε t ht
  have e1 : lowerB M K a hi t = Real.exp (-t) * (1 - M 0) - ∑ k ∈ Finset.range K, hi k * wk a k t := rfl
  have e2 : upperB M K a lo t = Real.exp (-t) * (1 - M 0) - ∑ k ∈ Finset.range K, lo k * wk a k t := rfl
  rw [e1, e2] at h2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem derivWithin_eq {f : ℝ → ℝ} {f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 4) : derivWithin f (Icc 0 4) s = f' s :=
  (hf s).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 4) s hs)

theorem C1On_of {f : ℝ → ℝ} {f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f') : C1On f :=
  ⟨fun s _ => (hf s).differentiableAt.differentiableWithinAt,
    hc.continuousOn.congr (fun s hs => derivWithin_eq hf s hs)⟩

theorem C1On_N : C1On N := C1On_of hasDerivAt_N (continuous_dnet WN)

theorem C1On_uhat : C1On uhat :=
  C1On_of hasDerivAt_uhat ((continuous_net WH).add (continuous_id.mul (continuous_dnet WH)))

/-- The certificate's data satisfy `Bounds` for a model whose residual is `r`. -/
theorem bounds_of_cert (M r : ℝ → ℝ) (hr : ∀ s ∈ Icc (0 : ℝ) 4, derivWithin M (Icc 0 4) s + M s - Real.exp (-s) = r s)
    (ok : Piece → Bool) (hok : ∀ x : Piece, ok x = true → ∀ s, pa x ≤ s → s ≤ pb x → plo x ≤ r s ∧ r s ≤ phi x)
    (num : ℤ) (hnum : 0 ≤ num) (L : List Piece) (G0 : Iv) (hG0 : memAt S (1 - M 0) G0)
    (hc : chainOK 0 L = true) (hs : seqOK num G0 G0 one L = true) (hall : L.all ok = true) :
    Bounds M L.length (ca L) (clo L) (chi L) ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -((num : ℝ) / 10000) ≤ lowerB M L.length (ca L) (chi L) t ∧
        upperB M L.length (ca L) (clo L) t ≤ (num : ℝ) / 10000 := by
  obtain ⟨h0, hK, hmono, hlh, hpc, hbd⟩ := cert_sound (1 - M 0) num hnum L G0 hG0 hc hs
  refine ⟨⟨h0, hK, hmono, hlh, ?_⟩, fun t ht => hbd t ht⟩
  intro k hk s hs
  obtain ⟨hk0, hk4, hmem, hka, hkb⟩ := hpc k hk
  have hx := List.all_eq_true.mp hall _ hmem
  have hs04 : s ∈ Icc (0 : ℝ) 4 := ⟨le_trans hk0 hs.1, le_trans hs.2 hk4⟩
  rw [hr s hs04]
  have := hok _ hx s (by rw [← hka]; exact hs.1) (by rw [← hkb]; exact hs.2)
  exact this

theorem memAt_gN0 : memAt S (1 - N 0) gN0 := by
  have h := memAt_add memAt_one (memAt_neg (memAt_net WN shape_WN (memAt_tI 0 0 0 (by norm_num) (by norm_num))))
  apply memAt_of_eq h
  unfold N
  ring

theorem memAt_gH0 : memAt S (1 - uhat 0) zero := by
  have h := memAt_zero (S : ℝ)
  apply memAt_of_eq h
  unfold uhat
  ring

theorem certN_length : certN.length = 508 := by
  decide +kernel

theorem certH_length : certH.length = 652 := by
  decide +kernel

end PINN
