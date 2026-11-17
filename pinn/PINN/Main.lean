import PINN.Defs

/-! # Certified error bounds for two networks solving `u' = -u + e^{-t}`, `u 0 = 1` on `[0, 4]`

* `IsSolution u` (`PINN.ODE`): `u 0 = 1` and, at every `t ∈ [0, 4]`, `u` has derivative `-u t + exp (-t)` within
  `[0, 4]` (one-sided at `0` and `4`).
* `C1On M` (`PINN.Defs`): `M` has a derivative within `[0, 4]` at every point of `[0, 4]`, and
  `M' = derivWithin M (Icc 0 4)` is continuous on `[0, 4]`.
* `wk a k t = ∫ s in Icc (a k) (a (k+1)) ∩ Icc 0 t, exp (-(t - s))` (`PINN.ODE`, Lebesgue set integral).
* `Bounds M K a lo hi` (`PINN.Defs`): `0 = a 0 < … < a K = 4`, `lo k ≤ hi k`, and
  `lo k ≤ M' s + M s - e^{-s} ≤ hi k` on `[a k, a (k+1)]` for `k < K`.
* `lowerB`, `upperB` (`PINN.Defs`): `e^{-t} (1 - M 0) - Σ_{k<K} hi k * wk a k t` and the same with `lo`.
* `N`, `Nh` (`PINN.Net`): the networks of `data/net.json` and `data/net_hardic.json`, weights over `2^16`;
  `uhat t = 1 + t * Nh t`.
* `certN`, `certH` (`PINN.DataN`, `PINN.DataH`): explicit lists of integer pieces `(p, q, l, h)`; piece `k` is
  `[p / 2^20, q / 2^20]` with `lo_k = l / 2^64`, `hi_k = h / 2^64`; `ca`, `clo`, `chi` read them by index
  (`cert_numbers`). -/

namespace PINN

open Set

/-- `N` written out: the integers of `data/net.json` over `2^16`. -/
theorem N_formula (t : ℝ) :
    N t = ∑ j ∈ Finset.range 32, ((NetW.W3.getD j 0 : ℤ) : ℝ) / 65536 *
      Real.tanh (∑ i ∈ Finset.range 32, (((NetW.W2.getD j []).getD i 0 : ℤ) : ℝ) / 65536 *
        Real.tanh (((NetW.W1.getD i 0 : ℤ) : ℝ) / 65536 * t + ((NetW.b1.getD i 0 : ℤ) : ℝ) / 65536) +
          ((NetW.b2.getD j 0 : ℤ) : ℝ) / 65536) + (NetW.b3 : ℝ) / 65536 := rfl

/-- `Ñ` written out: the integers of `data/net_hardic.json` over `2^16`. -/
theorem Nh_formula (t : ℝ) :
    Nh t = ∑ j ∈ Finset.range 32, ((NetH.W3.getD j 0 : ℤ) : ℝ) / 65536 *
      Real.tanh (∑ i ∈ Finset.range 32, (((NetH.W2.getD j []).getD i 0 : ℤ) : ℝ) / 65536 *
        Real.tanh (((NetH.W1.getD i 0 : ℤ) : ℝ) / 65536 * t + ((NetH.b1.getD i 0 : ℤ) : ℝ) / 65536) +
          ((NetH.b2.getD j 0 : ℤ) : ℝ) / 65536) + (NetH.b3 : ℝ) / 65536 := rfl

theorem uhat_formula (t : ℝ) : uhat t = 1 + t * Nh t := rfl

/-- Both weight sets have the shape 1 → 32 → 32 → 1. -/
theorem shapes : (NetW.W1.length = 32 ∧ NetW.b1.length = 32 ∧ NetW.W2.length = 32 ∧ NetW.b2.length = 32 ∧
      NetW.W3.length = 32 ∧ ∀ j < 32, (NetW.W2.getD j []).length = 32) ∧
    (NetH.W1.length = 32 ∧ NetH.b1.length = 32 ∧ NetH.W2.length = 32 ∧ NetH.b2.length = 32 ∧
      NetH.W3.length = 32 ∧ ∀ j < 32, (NetH.W2.getD j []).length = 32) :=
  ⟨⟨shape_WN.l1, shape_WN.l2, shape_WN.l3, shape_WN.l4, shape_WN.l5, shape_WN.rows⟩,
    ⟨shape_WH.l1, shape_WH.l2, shape_WH.l3, shape_WH.l4, shape_WH.l5, shape_WH.rows⟩⟩

/-- The residual-sum bound, for every `M` continuously differentiable on `[0, 4]` and every partition with
residual bounds. -/
theorem part1 (M : ℝ → ℝ) (hM : C1On M) (K : ℕ) (a lo hi : ℕ → ℝ) (hb : Bounds M K a lo hi)
    (u : ℝ → ℝ) (hu : IsSolution u) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    lowerB M K a hi t ≤ u t - M t ∧ u t - M t ≤ upperB M K a lo t :=
  residual_sum_bound M (derivWithin M (Icc 0 4)) (fun s hs => (hM.1 s hs).hasDerivWithinAt) hM.2 K a lo hi
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.2 u hu t ht

/-- `part1` with the derivative given explicitly: any continuous `M'` that is the derivative of `M` within `[0, 4]`. -/
theorem part1_explicit (M M' : ℝ → ℝ) (hM : ∀ t ∈ Icc (0 : ℝ) 4, HasDerivWithinAt M (M' t) (Icc 0 4) t)
    (hM' : ContinuousOn M' (Icc 0 4)) (K : ℕ) (a lo hi : ℕ → ℝ) (ha0 : a 0 = 0) (haK : a K = 4)
    (hmono : ∀ k < K, a k < a (k + 1)) (_hlh : ∀ k < K, lo k ≤ hi k)
    (hr : ∀ k < K, ∀ s ∈ Icc (a k) (a (k + 1)),
      lo k ≤ M' s + M s - Real.exp (-s) ∧ M' s + M s - Real.exp (-s) ≤ hi k)
    (u : ℝ → ℝ) (hu : IsSolution u) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    lowerB M K a hi t ≤ u t - M t ∧ u t - M t ≤ upperB M K a lo t :=
  residual_sum_bound M M' hM hM' K a lo hi ha0 haK hmono hr u hu t ht

/-- `part1` with Mathlib's `ContDiffOn ℝ 1 M (Icc 0 4)` as the hypothesis. -/
theorem part1_contDiffOn (M : ℝ → ℝ) (hM : ContDiffOn ℝ 1 M (Icc 0 4)) (K : ℕ) (a lo hi : ℕ → ℝ)
    (hb : Bounds M K a lo hi) (u : ℝ → ℝ) (hu : IsSolution u) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    lowerB M K a hi t ≤ u t - M t ∧ u t - M t ≤ upperB M K a lo t :=
  part1 M ⟨hM.differentiableOn_one,
    hM.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 4)) le_rfl⟩ K a lo hi hb u hu t ht

/-- For any model, the bounds of `part1` within `ε` everywhere give `|u - M| ≤ ε`. -/
theorem residual_route (M : ℝ → ℝ) (hM : C1On M) (ε : ℝ) (K : ℕ) (a lo hi : ℕ → ℝ) (hb : Bounds M K a lo hi)
    (hε : ∀ t ∈ Icc (0 : ℝ) 4, -ε ≤ lowerB M K a hi t ∧ upperB M K a lo t ≤ ε)
    (u : ℝ → ℝ) (hu : IsSolution u) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) : |u t - M t| ≤ ε :=
  residual_route_core M hM ε K a lo hi hb hε u hu t ht

/-- Both models are continuously differentiable on `[0, 4]`. -/
theorem models_C1 : C1On N ∧ C1On uhat := ⟨C1On_N, C1On_uhat⟩

/-- The numbers of a certificate list: `a_k = p / 2^20`, `lo_k = l / 2^64`, `hi_k = h / 2^64` from its `k`-th
piece `(p, q, l, h)` (`dflt = (2^22, 2^22, 0, 0)` past the end, so `a_K = 4`). -/
theorem cert_numbers (L : List Piece) (k : ℕ) :
    ca L k = ((L.getD k dflt).1 : ℝ) / 2 ^ 20 ∧ clo L k = ((L.getD k dflt).2.2.1 : ℝ) / 2 ^ 64 ∧
      chi L k = ((L.getD k dflt).2.2.2 : ℝ) / 2 ^ 64 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ca pa
    norm_num
  · unfold clo plo
    rw [S_real]
    norm_num
  · unfold chi phi
    rw [S_real]
    norm_num

/-- The 508 pieces of `certN` bound `N`'s own residual, and the bounds of `part1` built from them stay within
`2 / 10000` at every `t ∈ [0, 4]`. -/
theorem part2_named :
    certN.length = 508 ∧ Bounds N 508 (ca certN) (clo certN) (chi certN) ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(2 / 10000) ≤ lowerB N 508 (ca certN) (chi certN) t ∧
        upperB N 508 (ca certN) (clo certN) t ≤ 2 / 10000 := by
  have h := bounds_of_cert N rN (fun s hs => by rw [derivWithin_eq hasDerivAt_N s hs]; rfl) okRN okRN_sound 2
    (by norm_num) certN gN0 memAt_gN0 certN_chain certN_seq certN_all
  have e : ((2 : ℤ) : ℝ) / 10000 = 2 / 10000 := by norm_num
  rw [e, certN_length] at h
  exact ⟨certN_length, h⟩

/-- The 652 pieces of `certH` for `û`, within `3 / 10000`. -/
theorem part3_named :
    certH.length = 652 ∧ Bounds uhat 652 (ca certH) (clo certH) (chi certH) ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(3 / 10000) ≤ lowerB uhat 652 (ca certH) (chi certH) t ∧
        upperB uhat 652 (ca certH) (clo certH) t ≤ 3 / 10000 := by
  have h := bounds_of_cert uhat rH (fun s hs => by rw [derivWithin_eq hasDerivAt_uhat s hs]; unfold rH uhat Nh; ring)
    okRH okRH_sound 3 (by norm_num) certH zero memAt_gH0 certH_chain certH_seq certH_all
  have e : ((3 : ℤ) : ℝ) / 10000 = 3 / 10000 := by norm_num
  rw [e, certH_length] at h
  exact ⟨certH_length, h⟩

/-- The certificate `certN` is residual data only: it certifies, within `2 / 10000`, every continuously
differentiable model with `N`'s initial value whose own residual lies in its bounds. -/
theorem transfer_N (M : ℝ → ℝ) (hM : C1On M) (h0 : M 0 = N 0)
    (hr : ∀ k < 508, ∀ s ∈ Icc (ca certN k) (ca certN (k + 1)),
      clo certN k ≤ derivWithin M (Icc 0 4) s + M s - Real.exp (-s) ∧
        derivWithin M (Icc 0 4) s + M s - Real.exp (-s) ≤ chi certN k) :
    Bounds M 508 (ca certN) (clo certN) (chi certN) ∧
      (∀ t ∈ Icc (0 : ℝ) 4, -(2 / 10000) ≤ lowerB M 508 (ca certN) (chi certN) t ∧
        upperB M 508 (ca certN) (clo certN) t ≤ 2 / 10000) ∧
      ∀ u : ℝ → ℝ, IsSolution u → ∀ t ∈ Icc (0 : ℝ) 4, |u t - M t| ≤ 2 / 10000 := by
  have hG0 : memAt S (1 - M 0) gN0 := by rw [h0]; exact memAt_gN0
  obtain ⟨ha0, haK, hmono, hlh, _, hbd⟩ := cert_sound (1 - M 0) 2 (by norm_num) certN gN0 hG0 certN_chain certN_seq
  simp only [certN_length] at haK hmono hlh hbd
  have hb : Bounds M 508 (ca certN) (clo certN) (chi certN) := ⟨ha0, haK, hmono, hlh, hr⟩
  have e : ((2 : ℤ) : ℝ) / 10000 = 2 / 10000 := by norm_num
  rw [e] at hbd
  have hε : ∀ t ∈ Icc (0 : ℝ) 4, -(2 / 10000) ≤ lowerB M 508 (ca certN) (chi certN) t ∧
      upperB M 508 (ca certN) (clo certN) t ≤ 2 / 10000 := fun t ht => hbd t ht
  exact ⟨hb, hε, fun u hu t ht => residual_route_core M hM _ _ _ _ _ hb hε u hu t ht⟩

/-- The same for `certH`: every continuously differentiable model with `M 0 = 1` whose residual lies in its
bounds is within `3 / 10000` of every solution. -/
theorem transfer_H (M : ℝ → ℝ) (hM : C1On M) (h0 : M 0 = 1)
    (hr : ∀ k < 652, ∀ s ∈ Icc (ca certH k) (ca certH (k + 1)),
      clo certH k ≤ derivWithin M (Icc 0 4) s + M s - Real.exp (-s) ∧
        derivWithin M (Icc 0 4) s + M s - Real.exp (-s) ≤ chi certH k) :
    Bounds M 652 (ca certH) (clo certH) (chi certH) ∧
      (∀ t ∈ Icc (0 : ℝ) 4, -(3 / 10000) ≤ lowerB M 652 (ca certH) (chi certH) t ∧
        upperB M 652 (ca certH) (clo certH) t ≤ 3 / 10000) ∧
      ∀ u : ℝ → ℝ, IsSolution u → ∀ t ∈ Icc (0 : ℝ) 4, |u t - M t| ≤ 3 / 10000 := by
  have hG0 : memAt S (1 - M 0) zero := by rw [h0, sub_self]; exact memAt_zero _
  obtain ⟨ha0, haK, hmono, hlh, _, hbd⟩ := cert_sound (1 - M 0) 3 (by norm_num) certH zero hG0 certH_chain certH_seq
  simp only [certH_length] at haK hmono hlh hbd
  have hb : Bounds M 652 (ca certH) (clo certH) (chi certH) := ⟨ha0, haK, hmono, hlh, hr⟩
  have e : ((3 : ℤ) : ℝ) / 10000 = 3 / 10000 := by norm_num
  rw [e] at hbd
  have hε : ∀ t ∈ Icc (0 : ℝ) 4, -(3 / 10000) ≤ lowerB M 652 (ca certH) (chi certH) t ∧
      upperB M 652 (ca certH) (clo certH) t ≤ 3 / 10000 := fun t ht => hbd t ht
  exact ⟨hb, hε, fun u hu t ht => residual_route_core M hM _ _ _ _ _ hb hε u hu t ht⟩

/-- A partition and residual bounds for `N` (witness `certN`) whose `part1` bounds stay within `2 / 10000` on
`[0, 4]`; hence every solution is within `2 / 10000` of `N`. -/
theorem part2 :
    (∃ (K : ℕ) (a lo hi : ℕ → ℝ), Bounds N K a lo hi ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(2 / 10000) ≤ lowerB N K a hi t ∧ upperB N K a lo t ≤ 2 / 10000) ∧
    ∀ u : ℝ → ℝ, IsSolution u → ∀ t ∈ Icc (0 : ℝ) 4, |u t - N t| ≤ 2 / 10000 :=
  ⟨⟨508, ca certN, clo certN, chi certN, part2_named.2⟩,
    fun u hu t ht => residual_route_core N C1On_N _ _ _ _ _ part2_named.2.1 part2_named.2.2 u hu t ht⟩

/-- The same for `û = 1 + t Ñ` (witness `certH`) with `3 / 10000`. -/
theorem part3 :
    (∃ (K : ℕ) (a lo hi : ℕ → ℝ), Bounds uhat K a lo hi ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(3 / 10000) ≤ lowerB uhat K a hi t ∧ upperB uhat K a lo t ≤ 3 / 10000) ∧
    ∀ u : ℝ → ℝ, IsSolution u → ∀ t ∈ Icc (0 : ℝ) 4, |u t - uhat t| ≤ 3 / 10000 :=
  ⟨⟨652, ca certH, clo certH, chi certH, part3_named.2⟩,
    fun u hu t ht => residual_route_core uhat C1On_uhat _ _ _ _ _ part3_named.2.1 part3_named.2.2 u hu t ht⟩

/-- The solution set is not empty. -/
theorem solution_exists : IsSolution (fun t => (1 + t) * Real.exp (-t)) := sol_isSolution

/-- `part1`, `part2` and `part3`, with `part2` and `part3` also stated for the named certificates `certN`,
`certH`. -/
theorem main :
    (∀ (M : ℝ → ℝ), C1On M → ∀ (K : ℕ) (a lo hi : ℕ → ℝ), Bounds M K a lo hi →
      ∀ u : ℝ → ℝ, IsSolution u → ∀ t ∈ Icc (0 : ℝ) 4,
        lowerB M K a hi t ≤ u t - M t ∧ u t - M t ≤ upperB M K a lo t) ∧
    ((∃ (K : ℕ) (a lo hi : ℕ → ℝ), Bounds N K a lo hi ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(2 / 10000) ≤ lowerB N K a hi t ∧ upperB N K a lo t ≤ 2 / 10000) ∧
      ∀ u : ℝ → ℝ, IsSolution u → ∀ t ∈ Icc (0 : ℝ) 4, |u t - N t| ≤ 2 / 10000) ∧
    ((∃ (K : ℕ) (a lo hi : ℕ → ℝ), Bounds uhat K a lo hi ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(3 / 10000) ≤ lowerB uhat K a hi t ∧ upperB uhat K a lo t ≤ 3 / 10000) ∧
      ∀ u : ℝ → ℝ, IsSolution u → ∀ t ∈ Icc (0 : ℝ) 4, |u t - uhat t| ≤ 3 / 10000) ∧
    (Bounds N 508 (ca certN) (clo certN) (chi certN) ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(2 / 10000) ≤ lowerB N 508 (ca certN) (chi certN) t ∧
        upperB N 508 (ca certN) (clo certN) t ≤ 2 / 10000) ∧
    (Bounds uhat 652 (ca certH) (clo certH) (chi certH) ∧
      ∀ t ∈ Icc (0 : ℝ) 4, -(3 / 10000) ≤ lowerB uhat 652 (ca certH) (chi certH) t ∧
        upperB uhat 652 (ca certH) (clo certH) t ≤ 3 / 10000) :=
  ⟨fun M hM K a lo hi hb u hu t ht => part1 M hM K a lo hi hb u hu t ht, part2, part3, part2_named.2,
    part3_named.2⟩

end PINN
