import PINN.SoundBase

/-! # Soundness of the network enclosures and of the piece checks over `ℝ` -/

namespace PINN

open Finset Set

/-- A 1 → 32 → 32 → 1 shape. -/
structure Shape (P : Wts) : Prop where
  l1 : P.w1.length = 32
  l2 : P.c1.length = 32
  l3 : P.w2.length = 32
  l4 : P.c2.length = 32
  l5 : P.w3.length = 32
  rows : ∀ j < 32, (P.w2.getD j []).length = 32

theorem shape_WN : Shape WN :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem shape_WH : Shape WH :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem memAt_z1I (P : Wts) (i : ℕ) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    memAt S (z1 P i t) (z1I (P.w1.getD i 0) (P.c1.getD i 0) T) := by
  have h1 := memAt_mulZ (P.w1.getD i 0) hT
  have h2 : memAt S ((P.c1.getD i 0 : ℤ) : ℝ) (cst (P.c1.getD i 0 * S)) :=
    memAt_cst _ _ _ (by rw [Int.cast_mul])
  have h3 := memAt_add h1 h2
  apply memAt_downBy (by norm_num : (0 : ℤ) < 65536)
  apply memAt_of_eq h3
  unfold z1 w
  push_cast
  ring

theorem layer1_len (P : Wts) (hs : Shape P) (T : Iv) : (layer1 P T).length = 32 := by
  simp [layer1, List.length_zipWith, hs.l1, hs.l2]

theorem memAt_layer1 (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    ∀ i < 32, memAt S (Real.tanh (z1 P i t)) ((layer1 P T).getD i zero) := by
  intro i hi
  unfold layer1
  rw [getD_zipWith _ P.w1 P.c1 i zero 0 0 (by rw [hs.l1]; exact hi) (by rw [hs.l2]; exact hi)]
  exact memAt_tanh (memAt_z1I P i hT)

theorem memAt_layer2 (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    ∀ j < 32, memAt S (z2 P j t) ((layer2 P (layer1 P T)).getD j zero) := by
  intro j hj
  unfold layer2
  rw [getD_zipWith _ P.w2 P.c2 j zero [] 0 (by rw [hs.l3]; exact hj) (by rw [hs.l4]; exact hj)]
  have hr := hs.rows j hj
  have h1 := memAt_dotWI (P.w2.getD j []) (layer1 P T) (fun i => Real.tanh (z1 P i t))
    (by rw [hr, layer1_len P hs]) (by rw [hr]; exact memAt_layer1 P hs hT)
  rw [hr] at h1
  have h2 : memAt S (w (P.c2.getD j 0)) (cst (P.c2.getD j 0 * 281474976710656)) :=
    memAt_cst _ _ _ (by rw [S_real]; unfold w; push_cast; ring)
  exact memAt_add h1 h2

theorem layer2_len (P : Wts) (hs : Shape P) (A : List Iv) : (layer2 P A).length = 32 := by
  simp [layer2, List.length_zipWith, hs.l3, hs.l4]

theorem memAt_A2 (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    ∀ j < 32, memAt S (Real.tanh (z2 P j t)) (((layer2 P (layer1 P T)).map tanhI).getD j zero) := by
  intro j hj
  rw [getD_map tanhI _ j zero zero (by rw [layer2_len P hs]; exact hj)]
  exact memAt_tanh (memAt_layer2 P hs hT j hj)

theorem memAt_sqI {x : ℝ} {X : Iv} (hx : memAt S x X) : memAt S (x ^ 2) (sqI X) :=
  memAt_downBy S_pos_int (memAt_sqRaw hx)

theorem vList_len (P : Wts) (hs : Shape P) (A1 : List Iv) (h : A1.length = 32) : (vList P A1).length = 32 := by
  simp [vList, List.length_zipWith, hs.l1, h]

theorem qList_len (P : Wts) (hs : Shape P) (A1 : List Iv) (h : A1.length = 32) : (qList P A1).length = 32 := by
  simp [qList, List.length_zipWith, hs.l1, h]

theorem memAt_vList (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    ∀ i < 32, memAt S (w (P.w1.getD i 0) * (1 - Real.tanh (z1 P i t) ^ 2)) ((vList P (layer1 P T)).getD i zero) := by
  intro i hi
  have hA1 := memAt_layer1 P hs hT
  have hlen := layer1_len P hs T
  unfold vList
  rw [getD_zipWith _ P.w1 _ i zero 0 zero (by rw [hs.l1]; exact hi) (by rw [List.length_map, hlen]; exact hi)]
  rw [getD_map omsq _ i zero zero (by rw [hlen]; exact hi)]
  have h1 := memAt_mulZ (P.w1.getD i 0) (memAt_omsq (hA1 i hi))
  apply memAt_downBy (by norm_num : (0 : ℤ) < 65536)
  apply memAt_of_eq h1
  unfold w
  push_cast
  ring

theorem memAt_qList (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    ∀ i < 32, memAt S (q1 P i t) ((qList P (layer1 P T)).getD i zero) := by
  intro i hi
  have hA1 := memAt_layer1 P hs hT
  have hlen := layer1_len P hs T
  unfold qList
  rw [getD_zipWith _ P.w1 _ i zero 0 zero (by rw [hs.l1]; exact hi)
    (by rw [List.length_zipWith, List.length_map, hlen]; omega)]
  rw [getD_zipWith _ _ _ i zero zero zero (by rw [hlen]; exact hi) (by rw [List.length_map, hlen]; exact hi)]
  rw [getD_map omsq _ i zero zero (by rw [hlen]; exact hi)]
  have h0 := memAt_mul (hA1 i hi) (memAt_omsq (hA1 i hi))
  have h1 := memAt_mulZ (P.w1.getD i 0) h0
  have h2 := memAt_downBy (by norm_num : (0 : ℤ) < 65536) (s := S) (memAt_of_eq h1 (s' := S * 65536)
    (y := w (P.w1.getD i 0) * (Real.tanh (z1 P i t) * (1 - Real.tanh (z1 P i t) ^ 2))) (by unfold w; push_cast; ring))
  have h3 := memAt_mulZ (P.w1.getD i 0) h2
  apply memAt_downBy (by norm_num : (0 : ℤ) < 65536)
  apply memAt_of_eq h3
  unfold q1 w
  push_cast
  ring

theorem memAt_D (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    ∀ j < 32, memAt S (dz2 P j t) ((P.w2.map (fun row => dotWI row (vList P (layer1 P T)))).getD j zero) := by
  intro j hj
  rw [getD_map _ P.w2 j zero [] (by rw [hs.l3]; exact hj)]
  have hr := hs.rows j hj
  have h1 := memAt_dotWI (P.w2.getD j []) (vList P (layer1 P T))
    (fun i => w (P.w1.getD i 0) * (1 - Real.tanh (z1 P i t) ^ 2))
    (by rw [hr, vList_len P hs _ (layer1_len P hs T)]) (by rw [hr]; exact memAt_vList P hs hT)
  rw [hr] at h1
  exact h1

theorem memAt_D2 (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    ∀ j < 32, memAt S (dd2 P j t) ((P.w2.map (fun row => dotWI row (qList P (layer1 P T)))).getD j zero) := by
  intro j hj
  rw [getD_map _ P.w2 j zero [] (by rw [hs.l3]; exact hj)]
  have hr := hs.rows j hj
  have h1 := memAt_dotWI (P.w2.getD j []) (qList P (layer1 P T)) (fun i => q1 P i t)
    (by rw [hr, qList_len P hs _ (layer1_len P hs T)]) (by rw [hr]; exact memAt_qList P hs hT)
  rw [hr] at h1
  exact h1

theorem memAt_net (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    memAt S (net P t) (netAll P T).v := by
  show memAt S (net P t) (add (dotWI P.w3 ((layer2 P (layer1 P T)).map tanhI)) (cst (P.c3 * 281474976710656)))
  have h1 := memAt_dotWI P.w3 ((layer2 P (layer1 P T)).map tanhI) (fun j => Real.tanh (z2 P j t))
    (by simp [hs.l5, layer2_len P hs]) (by rw [hs.l5]; exact memAt_A2 P hs hT)
  rw [hs.l5] at h1
  have h2 : memAt S (w P.c3) (cst (P.c3 * 281474976710656)) :=
    memAt_cst _ _ _ (by rw [S_real]; unfold w; push_cast; ring)
  exact memAt_add h1 h2

theorem memAt_dnet (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    memAt S (dnet P t) (netAll P T).d := by
  show memAt S (dnet P t) (dotWI P.w3 (List.zipWith mul (((layer2 P (layer1 P T)).map tanhI).map omsq)
    (P.w2.map (fun row => dotWI row (vList P (layer1 P T))))))
  have hA2 := memAt_A2 P hs hT
  have hD := memAt_D P hs hT
  have hA2len : ((layer2 P (layer1 P T)).map tanhI).length = 32 := by simp [layer2_len P hs]
  have hm : ∀ j < 32, memAt S ((1 - Real.tanh (z2 P j t) ^ 2) * dz2 P j t)
      ((List.zipWith mul (((layer2 P (layer1 P T)).map tanhI).map omsq)
        (P.w2.map (fun row => dotWI row (vList P (layer1 P T))))).getD j zero) := by
    intro j hj
    rw [getD_zipWith _ _ _ j zero zero zero (by rw [List.length_map, hA2len]; exact hj)
      (by rw [List.length_map, hs.l3]; exact hj)]
    rw [getD_map omsq _ j zero zero (by rw [hA2len]; exact hj)]
    exact memAt_mul (memAt_omsq (hA2 j hj)) (hD j hj)
  have hlen : P.w3.length ≤ (List.zipWith mul (((layer2 P (layer1 P T)).map tanhI).map omsq)
      (P.w2.map (fun row => dotWI row (vList P (layer1 P T))))).length := by
    simp [List.length_zipWith, layer2_len P hs, hs.l3, hs.l5]
  have h := memAt_dotWI P.w3 _ (fun j => (1 - Real.tanh (z2 P j t) ^ 2) * dz2 P j t) hlen (by rw [hs.l5]; exact hm)
  rw [hs.l5] at h
  exact h

theorem memAt_d2net (P : Wts) (hs : Shape P) {t : ℝ} {T : Iv} (hT : memAt S t T) :
    memAt S (d2net P t) (netAll P T).d2 := by
  show memAt S (d2net P t) (mulZ (-2) (dotWI P.w3 (d2List ((layer2 P (layer1 P T)).map tanhI)
    (P.w2.map (fun row => dotWI row (vList P (layer1 P T))))
    (P.w2.map (fun row => dotWI row (qList P (layer1 P T)))))))
  have hA2 := memAt_A2 P hs hT
  have hD := memAt_D P hs hT
  have hD2 := memAt_D2 P hs hT
  have hA2len : ((layer2 P (layer1 P T)).map tanhI).length = 32 := by simp [layer2_len P hs]
  have hDlen : (P.w2.map (fun row => dotWI row (vList P (layer1 P T)))).length = 32 := by
    rw [List.length_map, hs.l3]
  have hD2len : (P.w2.map (fun row => dotWI row (qList P (layer1 P T)))).length = 32 := by
    rw [List.length_map, hs.l3]
  have hm : ∀ j < 32, memAt S ((1 - Real.tanh (z2 P j t) ^ 2) * (dd2 P j t + Real.tanh (z2 P j t) * dz2 P j t ^ 2))
      ((d2List ((layer2 P (layer1 P T)).map tanhI) (P.w2.map (fun row => dotWI row (vList P (layer1 P T))))
        (P.w2.map (fun row => dotWI row (qList P (layer1 P T))))).getD j zero) := by
    intro j hj
    unfold d2List
    rw [getD_zipWith _ _ _ j zero zero zero (by rw [List.length_map, hA2len]; exact hj)
      (by rw [List.length_zipWith, List.length_zipWith, hD2len, hA2len, hDlen]; omega)]
    rw [getD_map omsq _ j zero zero (by rw [hA2len]; exact hj)]
    rw [getD_zipWith _ _ _ j zero zero zero (by rw [hD2len]; exact hj)
      (by rw [List.length_zipWith, hA2len, hDlen]; omega)]
    rw [getD_zipWith _ _ _ j zero zero zero (by rw [hA2len]; exact hj) (by rw [hDlen]; exact hj)]
    exact memAt_mul (memAt_omsq (hA2 j hj)) (memAt_add (hD2 j hj) (memAt_mul (hA2 j hj) (memAt_sqI (hD j hj))))
  have hlen : P.w3.length ≤ (d2List ((layer2 P (layer1 P T)).map tanhI) (P.w2.map (fun row => dotWI row (vList P (layer1 P T))))
      (P.w2.map (fun row => dotWI row (qList P (layer1 P T))))).length := by
    simp [d2List, List.length_zipWith, layer2_len P hs, hs.l3, hs.l5]
  have h := memAt_dotWI P.w3 _ (fun j => (1 - Real.tanh (z2 P j t) ^ 2) * (dd2 P j t + Real.tanh (z2 P j t) * dz2 P j t ^ 2))
    hlen (by rw [hs.l5]; exact hm)
  rw [hs.l5] at h
  have h2 := memAt_mulZ (-2) h
  apply memAt_of_eq h2
  unfold d2net
  push_cast
  ring

theorem memAt_emI {t : ℝ} {T : Iv} (hT : memAt S t T) : memAt S (Real.exp (-t)) (emI T) :=
  memAt_exp (memAt_neg hT)

theorem memAt_rNI {t : ℝ} {T : Iv} (hT : memAt S t T) : memAt S (rN t) (rNI T) := by
  have h := memAt_add (memAt_add (memAt_dnet WN shape_WN hT) (memAt_net WN shape_WN hT)) (memAt_neg (memAt_emI hT))
  apply memAt_of_eq h
  unfold rN
  ring

theorem memAt_rdNI {t : ℝ} {T : Iv} (hT : memAt S t T) : memAt S (rN' t) (rdNI T) :=
  memAt_add (memAt_add (memAt_d2net WN shape_WN hT) (memAt_dnet WN shape_WN hT)) (memAt_emI hT)

theorem memAt_rHI {t : ℝ} {T : Iv} (hT : memAt S t T) : memAt S (rH t) (rHI T) := by
  have hv := memAt_net WH shape_WH hT
  have hd := memAt_dnet WH shape_WH hT
  have h := memAt_add (memAt_add (memAt_add hv (memAt_mul hT hd)) (memAt_add memAt_one (memAt_mul hT hv)))
    (memAt_neg (memAt_emI hT))
  apply memAt_of_eq h
  unfold rH
  ring

theorem memAt_rdHI {t : ℝ} {T : Iv} (hT : memAt S t T) : memAt S (rH' t) (rdHI T) := by
  have hv := memAt_net WH shape_WH hT
  have hd := memAt_dnet WH shape_WH hT
  have hd2 := memAt_d2net WH shape_WH hT
  have h := memAt_add (memAt_add (memAt_add (memAt_mulZ 2 hd) (memAt_mul hT hd2)) (memAt_add hv (memAt_mul hT hd)))
    (memAt_emI hT)
  apply memAt_of_eq h
  unfold rH'
  push_cast
  ring

theorem memAt_tI (p q : ℤ) (t : ℝ) (h1 : (p : ℝ) / 1048576 ≤ t) (h2 : t ≤ (q : ℝ) / 1048576) :
    memAt S t (tI p q) := by
  intro _
  simp only [tI]
  rw [S_real]
  push_cast
  constructor
  · rw [div_le_iff₀ (by norm_num)] at h1
    nlinarith
  · rw [le_div_iff₀ (by norm_num)] at h2
    nlinarith

/-! ## One piece -/

/-- The real numbers a piece stands for. -/
noncomputable def pa (x : Piece) : ℝ := (x.1 : ℝ) / 1048576

noncomputable def pb (x : Piece) : ℝ := (x.2.1 : ℝ) / 1048576

noncomputable def plo (x : Piece) : ℝ := (x.2.2.1 : ℝ) / (S : ℝ)

noncomputable def phi (x : Piece) : ℝ := (x.2.2.2 : ℝ) / (S : ℝ)

theorem okR2_sound (r r' : ℝ → ℝ) (hd : ∀ t, HasDerivAt r (r' t) t) (lo hi a b c : ℤ) (X D : Iv)
    (h : okR2 lo hi a b c X D = true) (hX : memAt S (r ((c : ℝ) / 1048576)) X)
    (hD : ∀ s : ℝ, (a : ℝ) / 1048576 ≤ s → s ≤ (b : ℝ) / 1048576 → memAt S (r' s) D)
    (t : ℝ) (h1 : (a : ℝ) / 1048576 ≤ t) (h2 : t ≤ (b : ℝ) / 1048576) :
    (lo : ℝ) / S ≤ r t ∧ r t ≤ (hi : ℝ) / S := by
  simp only [okR2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hXok, hDok⟩, hac⟩, hcb⟩, hlo⟩, hhi⟩ := h
  obtain ⟨x1, x2⟩ := hX hXok
  have hS := S_pos
  have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
  have hcb' : (c : ℝ) ≤ b := by exact_mod_cast hcb
  have hK1 : -(D.lo : ℝ) ≤ ((max (-D.lo) D.hi : ℤ) : ℝ) := by
    have := le_max_left (-D.lo) D.hi
    exact_mod_cast this
  have hK2 : (D.hi : ℝ) ≤ ((max (-D.lo) D.hi : ℤ) : ℝ) := by
    have := le_max_right (-D.lo) D.hi
    exact_mod_cast this
  have hlo' : (lo : ℝ) * 1048576 ≤ (X.lo : ℝ) * 1048576 - ((max (-D.lo) D.hi : ℤ) : ℝ) *
      ((max (c - a) (b - c) : ℤ) : ℝ) := by exact_mod_cast hlo
  have hhi' : (X.hi : ℝ) * 1048576 + ((max (-D.lo) D.hi : ℤ) : ℝ) * ((max (c - a) (b - c) : ℤ) : ℝ) ≤
      (hi : ℝ) * 1048576 := by exact_mod_cast hhi
  generalize ((max (-D.lo) D.hi : ℤ) : ℝ) = K at hK1 hK2 hlo' hhi'
  have hh1 : (c : ℝ) - a ≤ ((max (c - a) (b - c) : ℤ) : ℝ) := by
    have := le_max_left (c - a) (b - c)
    exact_mod_cast this
  have hh2 : (b : ℝ) - c ≤ ((max (c - a) (b - c) : ℤ) : ℝ) := by
    have := le_max_right (c - a) (b - c)
    exact_mod_cast this
  generalize ((max (c - a) (b - c) : ℤ) : ℝ) = H at hh1 hh2 hlo' hhi'
  have hbound : ∀ s ∈ Icc ((a : ℝ) / 1048576) ((b : ℝ) / 1048576), ‖r' s‖ ≤ K / S := by
    intro s hs
    obtain ⟨d1, d2⟩ := hD s hs.1 hs.2 hDok
    rw [Real.norm_eq_abs, le_div_iff₀ hS]
    have habs : |r' s * S| ≤ K := abs_le.mpr ⟨by linarith, by linarith⟩
    rwa [abs_mul, abs_of_pos hS] at habs
  have hcm : (c : ℝ) / 1048576 ∈ Icc ((a : ℝ) / 1048576) ((b : ℝ) / 1048576) :=
    ⟨by apply div_le_div_of_nonneg_right hac' (by norm_num),
     by apply div_le_div_of_nonneg_right hcb' (by norm_num)⟩
  have htm : t ∈ Icc ((a : ℝ) / 1048576) ((b : ℝ) / 1048576) := ⟨h1, h2⟩
  have hmvt := (convex_Icc ((a : ℝ) / 1048576) ((b : ℝ) / 1048576)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hd x).hasDerivWithinAt) hbound hcm htm
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hK0 : 0 ≤ K := by
    have := hbound _ hcm
    have h0 : 0 ≤ K / S := le_trans (norm_nonneg _) this
    exact (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => by linarith [h.2])
  have hdist : |t - (c : ℝ) / 1048576| ≤ H / 1048576 := by
    rw [abs_le]
    constructor
    · have : (a : ℝ) / 1048576 - (c : ℝ) / 1048576 = -(((c : ℝ) - a) / 1048576) := by ring
      have h3 : ((c : ℝ) - a) / 1048576 ≤ H / 1048576 := div_le_div_of_nonneg_right hh1 (by norm_num)
      linarith
    · have : (b : ℝ) / 1048576 - (c : ℝ) / 1048576 = ((b : ℝ) - c) / 1048576 := by ring
      have h3 : ((b : ℝ) - c) / 1048576 ≤ H / 1048576 := div_le_div_of_nonneg_right hh2 (by norm_num)
      linarith
  have hstep : |r t - r ((c : ℝ) / 1048576)| ≤ K / S * (H / 1048576) :=
    le_trans hmvt (mul_le_mul_of_nonneg_left hdist (div_nonneg hK0 hS.le))
  have hstep' : |r t - r ((c : ℝ) / 1048576)| * (S * 1048576) ≤ K * H := by
    have e : K / S * (H / 1048576) * (S * 1048576) = K * H := by field_simp
    calc |r t - r ((c : ℝ) / 1048576)| * (S * 1048576) ≤ K / S * (H / 1048576) * (S * 1048576) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = K * H := e
  have hP : (0 : ℝ) < S * 1048576 := by positivity
  constructor
  · have hdiff : -(K * H) ≤ (r t - r ((c : ℝ) / 1048576)) * (S * 1048576) := by
      have := neg_abs_le (r t - r ((c : ℝ) / 1048576))
      nlinarith
    rw [div_le_iff₀ hS]
    nlinarith
  · have hdiff : (r t - r ((c : ℝ) / 1048576)) * (S * 1048576) ≤ K * H := by
      have := le_abs_self (r t - r ((c : ℝ) / 1048576))
      nlinarith
    rw [le_div_iff₀ hS]
    nlinarith

theorem okR_sound (r r' : ℝ → ℝ) (R R' : Iv → Iv) (hd : ∀ t, HasDerivAt r (r' t) t)
    (hR : ∀ (t : ℝ) (T : Iv), memAt S t T → memAt S (r t) (R T))
    (hR' : ∀ (t : ℝ) (T : Iv), memAt S t T → memAt S (r' t) (R' T))
    (x : Piece) (h : okR R R' x = true) (t : ℝ) (h1 : pa x ≤ t) (h2 : t ≤ pb x) :
    plo x ≤ r t ∧ r t ≤ phi x :=
  okR2_sound r r' hd x.2.2.1 x.2.2.2 x.1 x.2.1 ((x.1 + x.2.1) / 2) _ _ h
    (hR _ _ (memAt_tI _ _ _ le_rfl le_rfl)) (fun s hs1 hs2 => hR' _ _ (memAt_tI _ _ _ hs1 hs2)) t h1 h2

theorem okRN_sound (x : Piece) (h : okRN x = true) (t : ℝ) (h1 : pa x ≤ t) (h2 : t ≤ pb x) :
    plo x ≤ rN t ∧ rN t ≤ phi x :=
  okR_sound rN rN' rNI rdNI hasDerivAt_rN (fun _ _ hT => memAt_rNI hT) (fun _ _ hT => memAt_rdNI hT) x h t h1 h2

theorem okRH_sound (x : Piece) (h : okRH x = true) (t : ℝ) (h1 : pa x ≤ t) (h2 : t ≤ pb x) :
    plo x ≤ rH t ∧ rH t ≤ phi x :=
  okR_sound rH rH' rHI rdHI hasDerivAt_rH (fun _ _ hT => memAt_rHI hT) (fun _ _ hT => memAt_rdHI hT) x h t h1 h2

end PINN
