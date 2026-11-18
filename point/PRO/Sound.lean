import Mathlib
import PRO.Mirror
import PRO.IntervalSound

/-! # Soundness of the interval forward pass

`p_sound : ∀ x, memAt S (p x) (pI x)`: for every prompt the real model's output lies in the interval
that `PRO.Mirror` computes. `bag_encl`, `gap_encl`, `point_encl` state what a `true` checker result
certifies. The list lemmas and the bag bookkeeping follow the tiny-transformer development. -/

namespace PRO

/-! ## Relational list lemmas -/

section ListRel

variable {α β γ δ ε ζ : Type*}

theorem f2_map_same {R : γ → δ → Prop} {f : α → γ} {g : α → δ} (H : ∀ a, R (f a) (g a)) :
    ∀ l : List α, List.Forall₂ R (l.map f) (l.map g)
  | [] => List.Forall₂.nil
  | a :: l => List.Forall₂.cons (H a) (f2_map_same H l)

theorem f2_map {R : α → β → Prop} {R' : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (H : ∀ a b, R a b → R' (f a) (g b)) :
    ∀ {l : List α} {L : List β}, List.Forall₂ R l L → List.Forall₂ R' (l.map f) (L.map g)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (H _ _ h) (f2_map H t)

theorem f2_zipWith_left {R : β → δ → Prop} {R' : ε → ζ → Prop} {f : α → β → ε} {g : α → δ → ζ}
    (H : ∀ a b d, R b d → R' (f a b) (g a d)) :
    ∀ (l : List α) {x : List β} {X : List δ}, List.Forall₂ R x X →
      List.Forall₂ R' (List.zipWith f l x) (List.zipWith g l X)
  | [], _, _, _ => by simp
  | _ :: _, _, _, .nil => by simp
  | a :: l, _, _, .cons h t => by
    simp only [List.zipWith_cons_cons]
    exact .cons (H _ _ _ h) (f2_zipWith_left H l t)

theorem f2_zipWith {R₁ : α → β → Prop} {R₂ : γ → δ → Prop} {R : ε → ζ → Prop}
    {f : α → γ → ε} {g : β → δ → ζ} (H : ∀ a b c d, R₁ a b → R₂ c d → R (f a c) (g b d)) :
    ∀ {l₁ : List α} {L₁ : List β} {l₂ : List γ} {L₂ : List δ}, List.Forall₂ R₁ l₁ L₁ →
      List.Forall₂ R₂ l₂ L₂ → List.Forall₂ R (List.zipWith f l₁ l₂) (List.zipWith g L₁ L₂)
  | _, _, _, _, .nil, _ => by simp
  | _, _, _, _, .cons _ _, .nil => by simp
  | _, _, _, _, .cons h t, .cons h' t' => by
    simp only [List.zipWith_cons_cons]
    exact .cons (H _ _ _ _ h h') (f2_zipWith H t t')

theorem f2_getD {R : α → β → Prop} {d : α} {D : β} (hd : R d D) :
    ∀ {l : List α} {L : List β}, List.Forall₂ R l L → ∀ i, R (l.getD i d) (L.getD i D)
  | _, _, .nil, _ => by simpa using hd
  | _, _, .cons h _, 0 => by simpa using h
  | _, _, .cons _ t, i + 1 => by simpa using f2_getD hd t i

theorem f2_append {R : α → β → Prop} :
    ∀ {l₁ : List α} {L₁ : List β} {l₂ : List α} {L₂ : List β},
      List.Forall₂ R l₁ L₁ → List.Forall₂ R l₂ L₂ → List.Forall₂ R (l₁ ++ l₂) (L₁ ++ L₂)
  | _, _, _, _, .nil, h => by simpa using h
  | _, _, _, _, .cons h t, h' => by simpa using ⟨h, f2_append t h'⟩

end ListRel

/-! ## Vectors and affine maps -/

theorem memAt_sum {s : ℝ} :
    ∀ {l : List ℝ} {L : List Iv}, List.Forall₂ (memAt s) l L → memAt s l.sum (sumI L)
  | _, _, .nil => by simpa [sumI] using memAt_zero s
  | _, _, .cons h t => by
    simp only [List.sum_cons, sumI, List.foldr_cons]
    exact memAt_add h (memAt_sum t)

theorem memAt_div {e z : ℝ} {E Zi : Iv} (he : memAt S e E) (hz : memAt S z⁻¹ Zi) :
    memAt S (e / z) (mul E Zi) := by
  rw [div_eq_mul_inv]
  exact memAt_mul he hz

/-- The real weight with integer numerator `z`: `z / 2^24`. -/
noncomputable def wt (z : ℤ) : ℝ := z / 16777216

theorem memAt_wtMul {x : ℝ} {X : Iv} (w : ℤ) (hx : memAt S x X) :
    memAt (S * ((16777216 : ℤ) : ℝ)) (wt w * x) (mulZ w X) := by
  have h := memAt_mulZ w hx
  intro hok
  obtain ⟨h1, h2⟩ := h hok
  have e : wt w * x * (S * ((16777216 : ℤ) : ℝ)) = w * x * S := by
    unfold wt
    push_cast
    field_simp
  rw [e]
  exact ⟨h1, h2⟩

theorem memAt_dotWI (row : List ℤ) {x : List ℝ} {X : List Iv} (hx : List.Forall₂ (memAt S) x X) :
    memAt S (dot (row.map wt) x) (dotWI row X) := by
  unfold dot dotWI
  apply memAt_downBy (by norm_num)
  apply memAt_sum
  rw [List.zipWith_map_left]
  exact f2_zipWith_left (R := memAt S) (R' := memAt (S * ((16777216 : ℤ) : ℝ)))
    (f := fun a b => wt a * b) (g := mulZ) (fun w _ _ h => memAt_wtMul w h) row hx

theorem memAt_dotI {x y : List ℝ} {X Y : List Iv} (hx : List.Forall₂ (memAt S) x X)
    (hy : List.Forall₂ (memAt S) y Y) : memAt S (dot x y) (dotI X Y) := by
  unfold dot dotI
  apply memAt_downBy S_pos_int
  apply memAt_sum
  exact f2_zipWith (R₁ := memAt S) (R₂ := memAt S) (R := memAt (S * S)) (f := fun a b => a * b)
    (g := mulRaw) (fun _ _ _ _ h h' => memAt_mulRaw h h') hx hy

theorem f2_vadd {x y : List ℝ} {X Y : List Iv} (hx : List.Forall₂ (memAt S) x X)
    (hy : List.Forall₂ (memAt S) y Y) : List.Forall₂ (memAt S) (vadd x y) (vaddI X Y) :=
  f2_zipWith (R₁ := memAt S) (R₂ := memAt S) (R := memAt S) (f := fun a b => a + b) (g := add)
    (fun _ _ _ _ h h' => memAt_add h h') hx hy

theorem f2_wt (l : List ℤ) : List.Forall₂ (memAt S) (l.map wt) (l.map ofW) :=
  f2_map_same (fun z => memAt_ofW z) l

theorem vec_eq (bits n : ℕ) : vec bits n = (rowNums bits n).map wt := by
  unfold vec rowNums
  rw [List.map_map]
  rfl

theorem f2_vec (bits n : ℕ) : List.Forall₂ (memAt S) (vec bits n) (vecI bits n) := by
  rw [vec_eq]
  exact f2_wt _

theorem f2_lin (rows : List ℕ) (n bias m : ℕ) {x : List ℝ} {X : List Iv}
    (hx : List.Forall₂ (memAt S) x X) :
    List.Forall₂ (memAt S) (lin (mat rows n) (vec bias m) x) (linI rows n bias m X) := by
  unfold lin linI mat
  rw [List.map_map]
  refine f2_vadd (f2_map_same (fun r => ?_) rows) (f2_vec bias m)
  show memAt S (dot (vec r n) x) (dotWI (rowNums r n) X)
  rw [vec_eq]
  exact memAt_dotWI _ hx

/-! ## LayerNorm -/

theorem memAt_pt (m : ℤ) : memAt S ((m : ℝ) / S) ⟨m, m, true⟩ := by
  intro _
  show (m : ℝ) ≤ (m : ℝ) / S * S ∧ (m : ℝ) / S * S ≤ (m : ℝ)
  rw [div_mul_cancel₀ _ S_pos.ne']
  exact ⟨le_refl _, le_refl _⟩

theorem memAt_EPS : memAt S (1 / 100000 : ℝ) EPS := by
  intro _
  have h1 := fdiv_mul_le S 100000 (by norm_num)
  have h2 := le_cdiv_mul S 100000 (by norm_num)
  show ((fdiv S 100000 : ℤ) : ℝ) ≤ 1 / 100000 * S ∧ 1 / 100000 * S ≤ ((cdiv S 100000 : ℤ) : ℝ)
  push_cast at h1 h2
  constructor <;> linarith

theorem memAt_mean {x : List ℝ} {X : List Iv} (hx : List.Forall₂ (memAt S) x X) :
    memAt S (lnMean x) (downBy 128 (sumI X)) := by
  apply memAt_downBy (by norm_num)
  intro hok
  obtain ⟨h1, h2⟩ := memAt_sum hx hok
  have e : lnMean x * ((S : ℝ) * ((128 : ℤ) : ℝ)) = x.sum * S := by
    unfold lnMean
    push_cast
    ring
  rw [e]
  exact ⟨h1, h2⟩

theorem S128_pos : (0 : ℤ) < S128 := by decide

theorem memAt_invStd {x : List ℝ} {X : List Iv} {μI : Iv} (hx : List.Forall₂ (memAt S) x X)
    (hμ : memAt S (lnMean x) μI) :
    memAt S (lnInvStd x) (recip (sqrtI (add (downBy S128
      (sumI (X.map fun t => mulRaw (add t (neg μI)) (add t (neg μI))))) EPS))) := by
  unfold lnInvStd
  apply memAt_recip
  apply memAt_sqrt
  refine memAt_add ?_ memAt_EPS
  have hsq : List.Forall₂ (memAt ((S : ℝ) * S)) (x.map fun t => (t - lnMean x) ^ 2)
      (X.map fun t => mulRaw (add t (neg μI)) (add t (neg μI))) :=
    f2_map (fun a A h => by
      have h3 := memAt_mulRaw (memAt_add h (memAt_neg hμ)) (memAt_add h (memAt_neg hμ))
      have e : (a - lnMean x) ^ 2 = (a + -lnMean x) * (a + -lnMean x) := by ring
      rw [e]
      exact h3) hx
  have hs := memAt_sum hsq
  apply memAt_downBy S128_pos
  intro hok
  obtain ⟨h1, h2⟩ := hs hok
  have c : ((S128 : ℤ) : ℝ) = (S : ℝ) * 128 := by
    unfold S128
    push_cast
    ring
  have e : (x.map fun t => (t - lnMean x) ^ 2).sum / 128 * ((S : ℝ) * ((S128 : ℤ) : ℝ)) =
      (x.map fun t => (t - lnMean x) ^ 2).sum * ((S : ℝ) * S) := by
    rw [c]
    ring
  rw [e]
  exact ⟨h1, h2⟩

theorem f2_layerNorm (g b : ℕ) {x : List ℝ} {X : List Iv} (hx : List.Forall₂ (memAt S) x X) :
    List.Forall₂ (memAt S) (layerNorm (vec g 128) (vec b 128) x) (layerNormI g b X) := by
  unfold layerNorm layerNormI
  simp only [stIv_eq]
  have hμ := memAt_mean hx
  have hr := memAt_invStd hx hμ
  refine f2_vadd ?_ (f2_vec b 128)
  rw [vec_eq, List.zipWith_map_left]
  refine f2_zipWith_left (R := memAt S) (R' := memAt S) ?_ (rowNums g 128) hx
  intro a t T h
  have h1 := memAt_add h (memAt_neg hμ)
  rw [← sub_eq_add_neg] at h1
  exact memAt_mul (memAt_ofW a) (memAt_mul h1 hr)

/-! ## Attention -/

theorem f2_rot (m : ℕ) {u : List ℝ} {U : List Iv} (hu : List.Forall₂ (memAt S) u U) :
    List.Forall₂ (memAt S) (rot m u) (rotI m U) := by
  unfold rot rotI
  refine f2_map_same (fun i => ?_) (List.range 32)
  have g := fun j => f2_getD (memAt_zero S) hu j
  by_cases h4 : i < 4
  · simp only [if_pos h4]
    have h1 := memAt_add (memAt_mul (g i) (memAt_cosT m i))
      (memAt_neg (memAt_mul (g (i + 4)) (memAt_sinT m i)))
    rw [← sub_eq_add_neg] at h1
    exact h1
  · by_cases h8 : i < 8
    · simp only [if_neg h4, if_pos h8]
      exact memAt_add (memAt_mul (g i) (memAt_cosT m (i - 4)))
        (memAt_mul (g (i - 4)) (memAt_sinT m (i - 4)))
    · simp only [if_neg h4, if_neg h8]
      exact g i

theorem f2_slice (a n : ℕ) {u : List ℝ} {U : List Iv} (h : List.Forall₂ (memAt S) u U) :
    List.Forall₂ (memAt S) (slice u a n) (sliceI U a n) :=
  List.forall₂_take n (List.forall₂_drop a h)

/-- Softmax is invariant under subtracting a constant from every score. -/
theorem softmax_shift (s : List ℝ) (m : ℝ) :
    (s.map fun x => Real.exp (x - m)).map (fun e => e / (s.map fun x => Real.exp (x - m)).sum) =
      (s.map Real.exp).map (fun e => e / (s.map Real.exp).sum) := by
  have hsum : (s.map fun x => Real.exp (x - m)).sum = (s.map Real.exp).sum * Real.exp (-m) := by
    rw [← List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro x _
    rw [sub_eq_add_neg, Real.exp_add]
  rw [hsum, List.map_map, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, sub_eq_add_neg, Real.exp_add]
  have : Real.exp (-m) ≠ 0 := (Real.exp_pos _).ne'
  rw [mul_div_mul_right _ _ this]

theorem f2_softmax {s : List ℝ} {Sc : List Iv} (hs : List.Forall₂ (memAt S) s Sc) :
    List.Forall₂ (memAt S) (softmax s) (softmaxI Sc) := by
  unfold softmaxI softmax
  simp only [stInt_eq, stList_eq, stIv_eq]
  rw [← softmax_shift s ((maxHi Sc : ℝ) / S)]
  have he : List.Forall₂ (memAt S) (s.map fun x => Real.exp (x - (maxHi Sc : ℝ) / S))
      (Sc.map fun t => expI (add t ⟨-maxHi Sc, -maxHi Sc, true⟩)) :=
    f2_map (fun a A h => by
      have h2 := memAt_add h (memAt_pt (-maxHi Sc))
      have e : a + ((-maxHi Sc : ℤ) : ℝ) / S = a - (maxHi Sc : ℝ) / S := by
        push_cast
        ring
      rw [e] at h2
      exact memAt_exp h2) hs
  have hZ := memAt_recip (memAt_sum he)
  exact f2_map (fun a A h => memAt_div h hZ) he

theorem memAt_32 : memAt S (32 : ℝ) ⟨32 * S, 32 * S, true⟩ := by
  intro _
  show ((32 * S : ℤ) : ℝ) ≤ 32 * S ∧ (32 : ℝ) * S ≤ ((32 * S : ℤ) : ℝ)
  push_cast
  exact ⟨le_refl _, le_refl _⟩

theorem f2_headOut (i h : ℕ) {q : List (List ℝ)} {Q : List (List Iv)}
    (hq : List.Forall₂ (List.Forall₂ (memAt S)) q Q) :
    List.Forall₂ (memAt S) (headOut i q h) (headOutI i Q h) := by
  unfold headOut headOutI
  simp only [stList_eq, stIv_eq]
  have gq := fun j => f2_getD (R := List.Forall₂ (memAt S)) List.Forall₂.nil hq j
  have hQ := f2_rot i (f2_slice (96 * h) 32 (gq i))
  have hrs : memAt S (Real.sqrt 32)⁻¹ (recip (sqrtI ⟨32 * S, 32 * S, true⟩)) :=
    memAt_recip (memAt_sqrt memAt_32)
  have hv : List.Forall₂ (List.Forall₂ (memAt S)) (q.map fun u => slice u (96 * h + 64) 32)
      (Q.map fun u => sliceI u (96 * h + 64) 32) :=
    f2_map (fun _ _ hu => f2_slice (96 * h + 64) 32 hu) hq
  exact f2_map_same (fun d => memAt_downBy S_pos_int (memAt_sum
    (f2_zipWith (R₁ := memAt S) (R₂ := List.Forall₂ (memAt S)) (R := memAt (S * S))
      (f := fun aj v => aj * v.getD d 0) (g := fun aj v => mulRaw aj (v.getD d zero))
      (fun _ _ _ _ h1 h2 => memAt_mulRaw h1 (f2_getD (memAt_zero S) h2 d))
      (f2_softmax (f2_map_same (fun j => memAt_mul (memAt_dotI hQ
        (f2_rot j (f2_slice (96 * h + 32) 32 (gq j)))) hrs) (List.range (i + 1))))
      hv))) (List.range 32)

theorem f2_attn (L : Layer) (i : ℕ) {q : List (List ℝ)} {Q : List (List Iv)}
    (hq : List.Forall₂ (List.Forall₂ (memAt S)) q Q) :
    List.Forall₂ (memAt S) (attn L i q) (attnI L i Q) := by
  unfold attn attnI
  simp only [stList_eq]
  exact f2_lin _ _ _ _ (f2_append (f2_append (f2_append (f2_headOut i 0 hq) (f2_headOut i 1 hq))
    (f2_headOut i 2 hq)) (f2_headOut i 3 hq))

theorem f2_mlp (L : Layer) {h : List ℝ} {H : List Iv} (hh : List.Forall₂ (memAt S) h H) :
    List.Forall₂ (memAt S) (mlp L h) (mlpI L H) := by
  unfold mlp mlpI
  simp only [stList_eq]
  exact f2_lin _ _ _ _ (f2_map (fun _ _ ha => memAt_gelu ha) (f2_lin _ _ _ _ hh))

/-! ## Layers and the output -/

theorem f2_block (L : Layer) {xs : List (List ℝ)} {Xs : List (List Iv)}
    (hx : List.Forall₂ (List.Forall₂ (memAt S)) xs Xs) :
    List.Forall₂ (List.Forall₂ (memAt S)) (block L xs) (blockI L Xs) := by
  unfold block blockI
  simp only [stLL_eq, stList_eq]
  rw [hx.length_eq]
  have hq : List.Forall₂ (List.Forall₂ (memAt S))
      (xs.map fun x => lin (mat L.qkvW 128) (vec L.qkvB 384)
        (layerNorm (vec L.ln1g 128) (vec L.ln1b 128) x))
      (Xs.map fun X => linI L.qkvW 128 L.qkvB 384 (layerNormI L.ln1g L.ln1b X)) :=
    f2_map (fun _ _ h => f2_lin _ _ _ _ (f2_layerNorm _ _ h)) hx
  refine f2_map_same (fun i => ?_) _
  have gx := f2_getD (R := List.Forall₂ (memAt S)) List.Forall₂.nil hx i
  exact f2_vadd (f2_vadd gx (f2_attn L i (List.forall₂_take (i + 1) hq)))
    (f2_mlp L (f2_layerNorm _ _ gx))

theorem memAt_final {xs : List (List ℝ)} {Xs : List (List Iv)}
    (hx : List.Forall₂ (List.Forall₂ (memAt S)) xs Xs) : memAt S (final xs) (finalI Xs) := by
  unfold final finalI
  simp only [stList_eq]
  rw [hx.length_eq]
  have hy := f2_layerNorm Bits.E.lnfg Bits.E.lnfb
    (f2_getD (R := List.Forall₂ (memAt S)) List.Forall₂.nil hx (Xs.length - 1))
  have h1 := memAt_dotWI (rowNums Bits.E.out_red 128) hy
  have h2 := memAt_dotWI (rowNums Bits.E.out_blue 128) hy
  rw [vec_eq Bits.E.out_red 128, vec_eq Bits.E.out_blue 128, sub_eq_add_neg]
  exact memAt_add h1 (memAt_neg h2)

theorem memAt_run : ∀ (Ls : List Layer) {xs : List (List ℝ)} {Xs : List (List Iv)},
    List.Forall₂ (List.Forall₂ (memAt S)) xs Xs →
      memAt S (final (Ls.foldl (fun xs L => block L xs) xs)) (runI Ls Xs)
  | [], _, _, hx => by simpa [runI] using memAt_final hx
  | L :: Ls, _, _, hx => by
    simp only [runI, stLL_eq, List.foldl_cons]
    exact memAt_run Ls (f2_block L hx)

/-- The interval forward pass encloses the logit difference, for every token sequence. -/
theorem logitDiff_sound (toks : List ℕ) : memAt S (logitDiff toks) (logitDiffI toks) := by
  unfold logitDiff logitDiffI
  simp only [stLL_eq]
  exact memAt_run layers (f2_map_same (fun t => f2_vec (embRow t) 128) toks)

/-- **Soundness.** For every prompt, `p x` lies in the interval `pI x`. -/
theorem p_sound (x : List Bool) : memAt S (p x) (pI x) := by
  have hp := memAt_recip (memAt_add memAt_one (memAt_exp (memAt_neg (logitDiff_sound (enc x)))))
  rw [← one_div] at hp
  exact hp

/-! ## From the Finset sum to the checker's list of orderings -/

theorem sum_ofFn (n : ℕ) (f : List Bool → ℝ) :
    ∑ x : Fin n → Bool, f (List.ofFn x) = ((allLists n).map f).sum := by
  induction n generalizing f with
  | zero => simp [allLists]
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ih (fun l => f (true :: l)), ih (fun l => f (false :: l))]
    simp [allLists, List.sum_append, List.map_map, Function.comp_def, add_comm]

theorem sum_map_ite {α : Type*} (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    ∀ l : List α, (l.map fun x => if P x then f x else 0).sum = ((l.filter fun x => decide (P x)).map f).sum
  | [] => by simp
  | a :: l => by by_cases h : P a <;> simp [h, sum_map_ite P f l]

theorem bag_sum (q : List Bool → ℝ) (n k : ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).count true = k), q (List.ofFn x) =
      ((orderings n k).map q).sum := by
  rw [Finset.sum_filter, sum_ofFn n (fun l => if l.count true = k then q l else 0), sum_map_ite]
  rfl

theorem length_filter_cons (A : List (List Bool)) (b : Bool) (k : ℕ) :
    ((A.map (List.cons b)).filter fun l => decide (l.count true = k)).length =
      (A.filter fun l => decide (l.count true + (if b then 1 else 0) = k)).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro l _
  cases b <;> simp

theorem orderings_length (n k : ℕ) : (orderings n k).length = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp [orderings, allLists]
  | succ n ih =>
    simp only [orderings, allLists, List.filter_append, List.length_append]
    rw [length_filter_cons, length_filter_cons]
    cases k with
    | zero =>
      have h0 : (List.filter (fun l => decide (l.count true + 1 = 0)) (allLists n)).length = 0 := by simp
      simp only [if_false, if_true, add_zero, Bool.false_eq_true]
      rw [h0, ← orderings, ih]
      simp
    | succ j =>
      simp only [if_false, if_true, add_zero, Bool.false_eq_true, Nat.add_right_cancel_iff]
      rw [← orderings, ← orderings, ih, ih, Nat.choose_succ_succ', add_comm]

/-! ## What the checkers certify -/

theorem TEN10_eq : (TEN10 : ℝ) = 10 ^ 10 := by norm_num [TEN10]

/-- A `true` bag check certifies a 10-digit enclosure of the uniform average of `p` over the
orderings of the bag `(n, k)`. -/
theorem bag_encl {n k : ℕ} (hk : k ≤ n) {a b : ℤ} (h : bagCheck n k a b = true) :
    (a : ℝ) / 10 ^ 10 ≤ (1 / (n.choose k : ℝ)) * ∑ x ∈ Finset.univ.filter
        (fun x : Fin n → Bool => (List.ofFn x).count true = k), p (List.ofFn x) ∧
      (1 / (n.choose k : ℝ)) * ∑ x ∈ Finset.univ.filter
        (fun x : Fin n → Bool => (List.ofFn x).count true = k), p (List.ofFn x) ≤ (b : ℝ) / 10 ^ 10 := by
  rw [bag_sum]
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hlen : (((orderings n k).length : ℤ) : ℝ) = n.choose k := by
    rw [orderings_length]; norm_cast
  simp only [bagCheck, stIv_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, h1⟩, h2⟩ := h
  obtain ⟨hT1, hT2⟩ := memAt_sum (f2_map_same (fun x => p_sound x) (orderings n k)) hok
  set T := ((orderings n k).map p).sum
  have hS := S_pos
  have h1' : (a : ℝ) * (n.choose k) * S ≤
      ((sumI ((orderings n k).map pI)).lo : ℝ) * 10 ^ 10 := by
    rw [← hlen, ← TEN10_eq]; exact_mod_cast h1
  have h2' : ((sumI ((orderings n k).map pI)).hi : ℝ) * 10 ^ 10 ≤
      (b : ℝ) * (n.choose k) * S := by
    rw [← hlen, ← TEN10_eq]; exact_mod_cast h2
  have k1 : (a : ℝ) * (n.choose k) ≤ T * 10 ^ 10 := by
    apply le_of_mul_le_mul_right _ hS
    nlinarith
  have k2 : T * 10 ^ 10 ≤ (b : ℝ) * (n.choose k) := by
    apply le_of_mul_le_mul_right _ hS
    nlinarith
  constructor
  · rw [div_le_iff₀ (by norm_num), one_div, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hC]
    linarith
  · rw [le_div_iff₀ (by norm_num), one_div, inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ hC]
    linarith

/-- What the two integer comparisons of a checker certify about a real `v` enclosed by `D`. -/
theorem encl_of_check {v : ℝ} {D : Iv} {a b : ℤ} (hv : memAt S v D) (hok : D.ok = true)
    (h1 : a * S ≤ D.lo * TEN10) (h2 : D.hi * TEN10 ≤ b * S) :
    (a : ℝ) / 10 ^ 10 ≤ v ∧ v ≤ (b : ℝ) / 10 ^ 10 := by
  obtain ⟨hD1, hD2⟩ := hv hok
  have hS := S_pos
  have h1' : (a : ℝ) * S ≤ (D.lo : ℝ) * 10 ^ 10 := by
    rw [← TEN10_eq]; exact_mod_cast h1
  have h2' : (D.hi : ℝ) * 10 ^ 10 ≤ (b : ℝ) * S := by
    rw [← TEN10_eq]; exact_mod_cast h2
  constructor
  · rw [div_le_iff₀ (by norm_num)]
    apply le_of_mul_le_mul_right _ hS
    nlinarith
  · rw [le_div_iff₀ (by norm_num)]
    apply le_of_mul_le_mul_right _ hS
    nlinarith

/-- A `true` gap check certifies a 10-digit enclosure of `p x - p x'`. -/
theorem gap_encl {x x' : List Bool} {a b : ℤ} (h : gapCheck x x' a b = true) :
    (a : ℝ) / 10 ^ 10 ≤ p x - p x' ∧ p x - p x' ≤ (b : ℝ) / 10 ^ 10 := by
  simp only [gapCheck, stIv_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, h1⟩, h2⟩ := h
  have hm := memAt_add (p_sound x) (memAt_neg (p_sound x'))
  rw [← sub_eq_add_neg] at hm
  exact encl_of_check hm hok h1 h2

/-- A `true` point check certifies a 10-digit enclosure of `p x`. -/
theorem point_encl {x : List Bool} {a b : ℤ} (h : pointCheck x a b = true) :
    (a : ℝ) / 10 ^ 10 ≤ p x ∧ p x ≤ (b : ℝ) / 10 ^ 10 := by
  simp only [pointCheck, stIv_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, h1⟩, h2⟩ := h
  exact encl_of_check (p_sound x) hok h1 h2

end PRO
