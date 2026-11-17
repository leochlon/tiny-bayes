import PINN.Sound
import PINN.ODE

/-! # From the kernel checks to certified error bounds

A certificate is a list of pieces `(a, b, lo, hi)` (`chainOK`: consecutive, from `0` to `4 * 2^20`). `seqOK`
propagates `g_j = (1 - M 0) - Σ_{k<j} lo_k (e^{a_{k+1}} - e^{a_k})` (and the same with `hi`) in interval arithmetic
and checks `e^{-a_j} g_j ≤ ε` at every partition point. On a piece the upper residual-sum bound is
`e^{-t} (g_j + lo_j e^{a_j}) - lo_j`, affine in `e^{-t}`, so its largest value on the piece is at an end. -/

namespace PINN

open Set

theorem pa_def (x : Piece) : pa x = (x.1 : ℝ) / 1048576 := rfl

/-- `Σ lo_k w_k(t)` and `Σ hi_k w_k(t)` over a list of pieces. -/
noncomputable def sumLo (L : List Piece) (t : ℝ) : ℝ := (L.map (fun x => plo x * wInt (pa x) (pb x) t)).sum

noncomputable def sumHi (L : List Piece) (t : ℝ) : ℝ := (L.map (fun x => phi x * wInt (pa x) (pb x) t)).sum

theorem sumLo_cons (x : Piece) (L : List Piece) (t : ℝ) :
    sumLo (x :: L) t = plo x * wInt (pa x) (pb x) t + sumLo L t := by
  simp [sumLo]

theorem sumHi_cons (x : Piece) (L : List Piece) (t : ℝ) :
    sumHi (x :: L) t = phi x * wInt (pa x) (pb x) t + sumHi L t := by
  simp [sumHi]

theorem chainOK_cons (a : ℤ) (x : Piece) (L : List Piece) :
    chainOK a (x :: L) = true ↔ x.1 = a ∧ x.1 < x.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧ chainOK x.2.1 L = true := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem chainOK_le : ∀ (L : List Piece) (a : ℤ), chainOK a L = true → a ≤ 4194304
  | [], a, h => by
    simp only [chainOK, decide_eq_true_eq] at h
    omega
  | x :: L, a, h => by
    rw [chainOK_cons] at h
    have := chainOK_le L x.2.1 h.2.2.2
    omega

theorem chainOK_mem : ∀ (L : List Piece) (a : ℤ), chainOK a L = true →
    ∀ y ∈ L, a ≤ y.1 ∧ y.1 < y.2.1 ∧ y.2.1 ≤ 4194304
  | [], _, _, y, hy => by simp at hy
  | x :: L, a, h, y, hy => by
    rw [chainOK_cons] at h
    obtain ⟨h1, h2, _, h4⟩ := h
    rcases List.mem_cons.mp hy with hy | hy
    · subst hy
      exact ⟨by omega, h2, chainOK_le L _ h4⟩
    · have := chainOK_mem L x.2.1 h4 y hy
      exact ⟨by omega, this.2.1, this.2.2⟩

theorem sumLo_zero : ∀ (L : List Piece) (a : ℤ), chainOK a L = true → 0 ≤ a →
    ∀ t : ℝ, t ≤ (a : ℝ) / 1048576 → sumLo L t = 0 ∧ sumHi L t = 0
  | [], _, _, _, t, _ => by simp [sumLo, sumHi]
  | x :: L, a, h, ha, t, ht => by
    rw [chainOK_cons] at h
    obtain ⟨h1, h2, _, h4⟩ := h
    have hxa : (0 : ℝ) ≤ pa x := by
      unfold pa
      have : (0 : ℝ) ≤ x.1 := by exact_mod_cast (show (0 : ℤ) ≤ x.1 by omega)
      positivity
    have hab : pa x ≤ pb x := by
      unfold pa pb
      have : (x.1 : ℝ) ≤ x.2.1 := by exact_mod_cast h2.le
      linarith
    have htx : t ≤ pa x := by
      unfold pa
      rw [h1]
      exact ht
    have hw : wInt (pa x) (pb x) t = 0 := by
      rw [wInt_formula _ _ _ hxa hab, min_eq_right (le_trans htx hab), min_eq_right htx, sub_self]
    have ih := sumLo_zero L x.2.1 h4 (by omega) t (by
      have : (a : ℝ) ≤ x.2.1 := by exact_mod_cast (show a ≤ x.2.1 by omega)
      have h5 : (a : ℝ) / 1048576 ≤ (x.2.1 : ℝ) / 1048576 := div_le_div_of_nonneg_right this (by norm_num)
      linarith)
    rw [sumLo_cons, sumHi_cons, hw, ih.1, ih.2]
    simp

theorem okPt_sound (num : ℤ) (hnum : 0 ≤ num) (G H E : Iv) (g h z : ℝ) (hok : okPt num G H E = true)
    (hG : memAt S g G) (hH : memAt S h H) (hE : memAt S (Real.exp z) E) :
    Real.exp (-z) * g ≤ (num : ℝ) / 10000 ∧ -((num : ℝ) / 10000) ≤ Real.exp (-z) * h := by
  simp only [okPt, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hGo, hHo⟩, hEo⟩, h1⟩, h2⟩ := hok
  obtain ⟨g1, g2⟩ := hG hGo
  obtain ⟨k1, k2⟩ := hH hHo
  obtain ⟨e1, e2⟩ := hE hEo
  have hS := S_pos
  have h1' : (10000 : ℝ) * G.hi ≤ num * E.lo := by exact_mod_cast h1
  have h2' : -((num : ℝ) * E.lo) ≤ 10000 * H.lo := by exact_mod_cast h2
  have hn : (0 : ℝ) ≤ num := by exact_mod_cast hnum
  have hez : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-z) := Real.exp_pos _
  have hup : g ≤ (num : ℝ) / 10000 * Real.exp z := by
    have : 10000 * (g * S) ≤ num * (Real.exp z * S) := by nlinarith
    have h3 : (10000 * g - num * Real.exp z) * S ≤ 0 := by nlinarith
    have h4 : 10000 * g - num * Real.exp z ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos hc hS
      linarith
    linarith
  have hlow : -((num : ℝ) / 10000 * Real.exp z) ≤ h := by
    have : -(num * (Real.exp z * S)) ≤ 10000 * (h * S) := by nlinarith
    have h3 : 0 ≤ (10000 * h + num * Real.exp z) * S := by nlinarith
    have h4 : 0 ≤ 10000 * h + num * Real.exp z := by
      by_contra hc
      push_neg at hc
      have := mul_neg_of_neg_of_pos hc hS
      linarith
    linarith
  constructor
  · calc Real.exp (-z) * g ≤ Real.exp (-z) * ((num : ℝ) / 10000 * Real.exp z) :=
          mul_le_mul_of_nonneg_left hup hpos.le
      _ = (num : ℝ) / 10000 * (Real.exp (-z) * Real.exp z) := by ring
      _ = (num : ℝ) / 10000 := by rw [hez, mul_one]
  · calc -((num : ℝ) / 10000) = Real.exp (-z) * -((num : ℝ) / 10000 * Real.exp z) := by
          rw [show Real.exp (-z) * -((num : ℝ) / 10000 * Real.exp z) =
            -((num : ℝ) / 10000 * (Real.exp (-z) * Real.exp z)) by ring, hez, mul_one]
      _ ≤ Real.exp (-z) * h := mul_le_mul_of_nonneg_left hlow hpos.le

theorem memAt_plo (x : Piece) : memAt S (plo x) (cst x.2.2.1) :=
  memAt_cst _ _ _ (by unfold plo; field_simp [S_pos.ne'])

theorem memAt_phi (x : Piece) : memAt S (phi x) (cst x.2.2.2) :=
  memAt_cst _ _ _ (by unfold phi; field_simp [S_pos.ne'])

/-- One piece of the pass: the bounds on `[a, b]` from those at its ends. -/
theorem piece_bound (A B t g lo e : ℝ) (hAt : A ≤ t) (htB : t ≤ B)
    (hA : Real.exp (-A) * g ≤ e) (hB : Real.exp (-B) * (g - lo * (Real.exp B - Real.exp A)) ≤ e) :
    Real.exp (-t) * g - lo * (Real.exp (-(t - t)) - Real.exp (-(t - A))) ≤ e := by
  have h1 : Real.exp (-(t - A)) = Real.exp (-t) * Real.exp A := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-B) * Real.exp B = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (-A) * Real.exp A = 1 := by rw [← Real.exp_add]; simp
  have hBt : Real.exp (-B) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  have htA : Real.exp (-t) ≤ Real.exp (-A) := Real.exp_le_exp.mpr (by linarith)
  rw [sub_self, neg_zero, Real.exp_zero, h1]
  set C := g + lo * Real.exp A
  have eA : Real.exp (-A) * g = Real.exp (-A) * C - lo := by
    simp only [C]
    rw [mul_add, ← mul_assoc, mul_comm (Real.exp (-A)) lo, mul_assoc, h3]
    ring
  have eB : Real.exp (-B) * (g - lo * (Real.exp B - Real.exp A)) = Real.exp (-B) * C - lo := by
    simp only [C]
    have : Real.exp (-B) * (g - lo * (Real.exp B - Real.exp A)) =
        Real.exp (-B) * (g + lo * Real.exp A) - lo * (Real.exp (-B) * Real.exp B) := by ring
    rw [this, h2]
    ring
  have et : Real.exp (-t) * g - lo * (1 - Real.exp (-t) * Real.exp A) = Real.exp (-t) * C - lo := by
    simp only [C]
    ring
  rw [et]
  rcases le_total 0 C with hC | hC
  · have := mul_le_mul_of_nonneg_right htA hC
    linarith
  · have := mul_le_mul_of_nonpos_right hBt hC
    linarith

/-- The pass, by induction over the pieces. -/
theorem seq_sound (num : ℤ) (hnum : 0 ≤ num) : ∀ (L : List Piece) (a : ℤ) (G H E : Iv) (g h : ℝ),
    0 ≤ a → chainOK a L = true → seqOK num G H E L = true → memAt S g G → memAt S h H →
    memAt S (Real.exp ((a : ℝ) / 1048576)) E →
    ∀ t : ℝ, (a : ℝ) / 1048576 ≤ t → t ≤ 4 →
      Real.exp (-t) * g - sumLo L t ≤ (num : ℝ) / 10000 ∧
        -((num : ℝ) / 10000) ≤ Real.exp (-t) * h - sumHi L t
  | [], a, G, H, E, g, h, _, hc, hs, hG, hH, hE, t, h1, h2 => by
    simp only [chainOK, decide_eq_true_eq] at hc
    have ha : (a : ℝ) / 1048576 = 4 := by rw [hc]; norm_num
    have ht : t = (a : ℝ) / 1048576 := by linarith
    have hs' : okPt num G H E = true := hs
    have := okPt_sound num hnum G H E g h _ hs' hG hH hE
    rw [ht]
    simp only [sumLo, sumHi, List.map_nil, List.sum_nil, sub_zero]
    exact this
  | x :: L, a, G, H, E, g, h, ha, hc, hs, hG, hH, hE, t, h1, h2 => by
    rw [chainOK_cons] at hc
    obtain ⟨hx1, hx2, _, hc4⟩ := hc
    have hs' : (okPt num G H E && seqOK num (add G (neg (mul (cst x.2.2.1) (add (expI (tI x.2.1 x.2.1)) (neg E)))))
        (add H (neg (mul (cst x.2.2.2) (add (expI (tI x.2.1 x.2.1)) (neg E))))) (expI (tI x.2.1 x.2.1)) L) = true := hs
    rw [Bool.and_eq_true] at hs'
    obtain ⟨hpt, hrest⟩ := hs'
    set A : ℝ := pa x with hAdef
    set B : ℝ := pb x with hBdef
    have hAa : A = (a : ℝ) / 1048576 := by rw [hAdef, pa_def, hx1]
    have hA0 : 0 ≤ A := by
      rw [hAa]
      have : (0 : ℝ) ≤ a := by exact_mod_cast ha
      positivity
    have hAB : A < B := by
      rw [hAdef, hBdef]
      unfold pa pb
      have : (x.1 : ℝ) < x.2.1 := by exact_mod_cast hx2
      linarith
    have hB4 : B ≤ 4 := by
      have := chainOK_le L x.2.1 hc4
      have h' : (x.2.1 : ℝ) ≤ 4194304 := by exact_mod_cast this
      rw [hBdef]
      unfold pb
      linarith
    have hE' : memAt S (Real.exp B) (expI (tI x.2.1 x.2.1)) :=
      memAt_exp (memAt_tI _ _ _ le_rfl le_rfl)
    have hdE : memAt S (Real.exp B - Real.exp A) (add (expI (tI x.2.1 x.2.1)) (neg E)) := by
      have := memAt_add hE' (memAt_neg hE)
      rw [← hAa] at this
      apply memAt_of_eq this
      ring
    have hG' := memAt_add hG (memAt_neg (memAt_mul (memAt_plo x) hdE))
    have hH' := memAt_add hH (memAt_neg (memAt_mul (memAt_phi x) hdE))
    have ih := seq_sound num hnum L x.2.1 _ _ _ _ _ (by omega) hc4 hrest hG' hH' hE'
    have hptA := okPt_sound num hnum G H E g h _ hpt hG hH hE
    rw [← hAa] at hptA
    rw [sumLo_cons, sumHi_cons, wInt_formula A B t hA0 hAB.le]
    have hzero := sumLo_zero L x.2.1 hc4 (by omega)
    rcases le_total t B with htB | htB
    · -- inside the piece
      have hz := hzero t htB
      have hzB := hzero B le_rfl
      have hiB := ih B le_rfl hB4
      rw [hzB.1, hzB.2, sub_zero, sub_zero] at hiB
      rw [hz.1, hz.2, add_zero, add_zero, min_eq_right htB, min_eq_left (show A ≤ t by rw [hAa]; exact h1)]
      constructor
      · have := piece_bound A B t g (plo x) ((num : ℝ) / 10000) (by rw [hAa]; exact h1) htB hptA.1
          (by have := hiB.1; rw [show g + -(plo x * (Real.exp B - Real.exp A)) =
            g - plo x * (Real.exp B - Real.exp A) by ring] at this; exact this)
        exact this
      · have := piece_bound A B t (-h) (-phi x) ((num : ℝ) / 10000) (by rw [hAa]; exact h1) htB
          (by have := hptA.2; linarith)
          (by have := hiB.2; nlinarith [this])
        linarith
    · -- past the piece
      have hiT := ih t htB h2
      rw [min_eq_left htB, min_eq_left (le_trans hAB.le htB)]
      have e1 : Real.exp (-(t - B)) - Real.exp (-(t - A)) = Real.exp (-t) * (Real.exp B - Real.exp A) := by
        rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
        ring_nf
      rw [e1]
      constructor
      · have := hiT.1
        nlinarith [this]
      · have := hiT.2
        nlinarith [this]

/-- The default piece past the end of a list: `a = b = 4 * 2^20`. -/
def dflt : Piece := (4194304, 4194304, 0, 0)

theorem sum_getD (f : Piece → ℝ) : ∀ L : List Piece,
    ∑ k ∈ Finset.range L.length, f (L.getD k dflt) = (L.map f).sum
  | [] => by simp
  | x :: L => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_getD f L]
    ring

theorem chain_getD : ∀ (L : List Piece) (a : ℤ), chainOK a L = true → ∀ k < L.length,
    (L.getD k dflt).1 < (L.getD k dflt).2.1 ∧ (L.getD k dflt).2.2.1 ≤ (L.getD k dflt).2.2.2 ∧
      (L.getD (k + 1) dflt).1 = (L.getD k dflt).2.1 ∧ L.getD k dflt ∈ L
  | [], _, _, k, hk => by simp at hk
  | x :: L, a, h, k, hk => by
    rw [chainOK_cons] at h
    obtain ⟨_, h2, h3, h4⟩ := h
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨h2, h3, ?_, List.mem_cons_self⟩
      cases L with
      | nil =>
        simp only [chainOK, decide_eq_true_eq] at h4
        simp [dflt, h4]
      | cons y L' =>
        rw [chainOK_cons] at h4
        simp only [List.getD_cons_zero]
        exact h4.1
    | succ n =>
      simp only [List.getD_cons_succ]
      have := chain_getD L x.2.1 h4 n (by simp at hk; omega)
      exact ⟨this.1, this.2.1, this.2.2.1, List.mem_cons_of_mem _ this.2.2.2⟩

theorem chain_head (L : List Piece) (h : chainOK 0 L = true) : (L.getD 0 dflt).1 = 0 := by
  cases L with
  | nil => simp [chainOK] at h
  | cons x L =>
    rw [chainOK_cons] at h
    simp only [List.getD_cons_zero]
    exact h.1

/-- The certificate's partition and bounds as functions of the index. -/
noncomputable def ca (L : List Piece) (k : ℕ) : ℝ := pa (L.getD k dflt)

noncomputable def clo (L : List Piece) (k : ℕ) : ℝ := plo (L.getD k dflt)

noncomputable def chi (L : List Piece) (k : ℕ) : ℝ := phi (L.getD k dflt)

theorem ca_succ (L : List Piece) (a : ℤ) (h : chainOK a L = true) (k : ℕ) (hk : k < L.length) :
    ca L (k + 1) = pb (L.getD k dflt) := by
  unfold ca pa pb
  rw [(chain_getD L a h k hk).2.2.1]

theorem sum_ca (L : List Piece) (a : ℤ) (h : chainOK a L = true) (c : Piece → ℝ) (t : ℝ) :
    ∑ k ∈ Finset.range L.length, c (L.getD k dflt) * wk (ca L) k t =
      (L.map (fun x => c x * wInt (pa x) (pb x) t)).sum := by
  rw [← sum_getD (fun x => c x * wInt (pa x) (pb x) t) L]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  show c (L.getD k dflt) * wInt (ca L k) (ca L (k + 1)) t = _
  rw [ca_succ L a h k hk']
  rfl

/-- What a certificate gives: a partition of `[0, 4]`, `lo ≤ hi`, pieces inside `[0, 4]`, and the residual-sum
bounds within `num / 10000` at every `t ∈ [0, 4]`. -/
theorem cert_sound (g0 : ℝ) (num : ℤ) (hnum : 0 ≤ num) (L : List Piece) (G0 : Iv) (hG0 : memAt S g0 G0)
    (hc : chainOK 0 L = true) (hs : seqOK num G0 G0 one L = true) :
    ca L 0 = 0 ∧ ca L L.length = 4 ∧ (∀ k < L.length, ca L k < ca L (k + 1)) ∧
      (∀ k < L.length, clo L k ≤ chi L k) ∧
      (∀ k < L.length, 0 ≤ ca L k ∧ ca L (k + 1) ≤ 4 ∧ L.getD k dflt ∈ L ∧
        ca L k = pa (L.getD k dflt) ∧ ca L (k + 1) = pb (L.getD k dflt)) ∧
      ∀ t ∈ Icc (0 : ℝ) 4,
        -((num : ℝ) / 10000) ≤ Real.exp (-t) * g0 - ∑ k ∈ Finset.range L.length, chi L k * wk (ca L) k t ∧
        Real.exp (-t) * g0 - ∑ k ∈ Finset.range L.length, clo L k * wk (ca L) k t ≤ (num : ℝ) / 10000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ca pa
    rw [chain_head L hc]
    simp
  · unfold ca pa
    rw [List.getD_eq_default _ _ le_rfl]
    simp [dflt]
    norm_num
  · intro k hk
    rw [ca_succ L 0 hc k hk]
    unfold ca pa pb
    have := (chain_getD L 0 hc k hk).1
    have h' : ((L.getD k dflt).1 : ℝ) < (L.getD k dflt).2.1 := by exact_mod_cast this
    linarith
  · intro k hk
    unfold clo chi plo phi
    have := (chain_getD L 0 hc k hk).2.1
    have h' : ((L.getD k dflt).2.2.1 : ℝ) ≤ (L.getD k dflt).2.2.2 := by exact_mod_cast this
    exact div_le_div_of_nonneg_right h' S_pos.le
  · intro k hk
    have hm := (chain_getD L 0 hc k hk).2.2.2
    have hr := chainOK_mem L 0 hc _ hm
    refine ⟨?_, ?_, hm, rfl, ca_succ L 0 hc k hk⟩
    · unfold ca pa
      have : (0 : ℝ) ≤ (L.getD k dflt).1 := by exact_mod_cast hr.1
      positivity
    · rw [ca_succ L 0 hc k hk]
      unfold pb
      have : ((L.getD k dflt).2.1 : ℝ) ≤ 4194304 := by exact_mod_cast hr.2.2
      linarith
  · intro t ht
    have h0 : memAt S (Real.exp (((0 : ℤ) : ℝ) / 1048576)) one := by
      simp only [Int.cast_zero, zero_div, Real.exp_zero]
      exact memAt_one
    have := seq_sound num hnum L 0 G0 G0 one g0 g0 le_rfl hc hs hG0 hG0 h0 t (by simp [ht.1]) ht.2
    have e1 := sum_ca L 0 hc plo t
    have e2 := sum_ca L 0 hc phi t
    unfold clo chi
    rw [e1, e2]
    exact ⟨this.2, this.1⟩

end PINN
