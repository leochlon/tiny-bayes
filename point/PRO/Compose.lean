import Mathlib
import PRO.Sound
import PRO.Checks

/-! # Checked boxes enclose the real model

`layer_ok`: if the boxes `Bx` enclose the residual vectors of all positions before a layer and the
four kinds of checks of `PRO.Checks` hold at every position, then the boxes `Bo` enclose the residual
vectors after the layer. `p_encl_of_boxes`: an enclosure of `p x` from the boxes after the last layer. -/

namespace PRO

theorem f2_sub {x : List ℝ} {Xs : List Iv} (hx : List.Forall₂ (memAt S) x Xs) :
    ∀ Bs : List Iv, allSub Xs Bs = true → List.Forall₂ (memAt S) x Bs := by
  induction hx with
  | nil =>
    intro Bs h
    cases Bs with
    | nil => exact .nil
    | cons B Bs => simp [allSub] at h
  | cons hxa _ ih =>
    intro Bs h
    cases Bs with
    | nil => simp [allSub] at h
    | cons B Bs =>
      simp only [allSub, Bool.and_eq_true] at h
      exact .cons (memAt_inB hxa h.1) (ih Bs h.2)

theorem f2_of_getD {α β : Type*} {R : α → β → Prop} (a : α) (b : β) :
    ∀ {l : List α} {L : List β}, l.length = L.length →
      (∀ i, i < l.length → R (l.getD i a) (L.getD i b)) → List.Forall₂ R l L
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l, y :: L, h, H => by
    refine .cons ?_ (f2_of_getD a b (by simpa using h) fun i hi => ?_)
    · simpa using H 0 (by simp)
    · simpa using H (i + 1) (by simpa using hi)

/-- The `qkv` vector of one position. -/
noncomputable def qkvR (L : Layer) (x : List ℝ) : List ℝ :=
  lin (mat L.qkvW 128) (vec L.qkvB 384) (layerNorm (vec L.ln1g 128) (vec L.ln1b 128) x)

/-- The output of a layer at position `i`. -/
noncomputable def blockAt (L : Layer) (xs : List (List ℝ)) (i : ℕ) : List ℝ :=
  vadd (vadd (xs.getD i []) (attn L i ((xs.map (qkvR L)).take (i + 1))))
    (mlp L (layerNorm (vec L.ln2g 128) (vec L.ln2b 128) (xs.getD i [])))

theorem block_eq (L : Layer) (xs : List (List ℝ)) :
    block L xs = (List.range xs.length).map (blockAt L xs) := rfl

/-- **One layer.** Checked boxes after a layer enclose the layer's output at every position. -/
theorem layer_ok (L : Layer) {xs : List (List ℝ)} {Bx Bq Ba Bh Bo : List (List Iv)}
    (hx : List.Forall₂ (List.Forall₂ (memAt S)) xs Bx)
    (hlq : Bq.length = Bx.length) (hlo : Bo.length = Bx.length)
    (hq : ∀ i, i < Bx.length → qCheck L (Bx.getD i []) (Bq.getD i []) = true)
    (ha : ∀ i, i < Bx.length → aCheck L i (Bq.take (i + 1)) (Ba.getD i []) = true)
    (hh : ∀ i, i < Bx.length → hCheck L (Bx.getD i []) (Bh.getD i []) = true)
    (ho : ∀ i, i < Bx.length →
      oCheck L (Bx.getD i []) (Ba.getD i []) (Bh.getD i []) (Bo.getD i []) = true) :
    List.Forall₂ (List.Forall₂ (memAt S)) (block L xs) Bo := by
  have hlen := hx.length_eq
  have gx := fun i => f2_getD (R := List.Forall₂ (memAt S)) List.Forall₂.nil hx i
  have hQ : List.Forall₂ (List.Forall₂ (memAt S)) (xs.map (qkvR L)) Bq := by
    refine f2_of_getD (qkvR L []) [] (by simp [hlen, hlq]) fun i hi => ?_
    rw [List.getD_map (f := qkvR L)]
    have hi' : i < Bx.length := by simpa [hlen] using hi
    have hc := hq i hi'
    simp only [qCheck, stList_eq] at hc
    unfold qkvR
    exact f2_sub (f2_lin L.qkvW 128 L.qkvB 384 (f2_layerNorm L.ln1g L.ln1b (gx i))) _ hc
  rw [block_eq, hlen]
  refine f2_of_getD (blockAt L xs 0) [] (by simp [hlo]) fun i hi => ?_
  have hi' : i < Bx.length := by simpa using hi
  rw [List.getD_map (f := blockAt L xs)]
  have e : (List.range Bx.length).getD i 0 = i := by
    have h1 : i < (List.range Bx.length).length := by simpa using hi'
    rw [List.getD_eq_getElem _ _ h1]
    simp
  rw [e]
  have hac := ha i hi'
  simp only [aCheck] at hac
  have hatt := f2_sub (f2_attn L i (List.forall₂_take (i + 1) hQ)) _ hac
  have hc := hh i hi'
  simp only [hCheck, stList_eq] at hc
  have hhid := f2_sub (f2_map (R := memAt S) (R' := memAt S) (f := gelu) (g := geluI)
    (fun _ _ h => memAt_gelu h)
    (f2_lin L.fcW 128 L.fcB 512 (f2_layerNorm L.ln2g L.ln2b (gx i)))) _ hc
  have hmlp : List.Forall₂ (memAt S)
      (mlp L (layerNorm (vec L.ln2g 128) (vec L.ln2b 128) (xs.getD i [])))
      (linI L.pjW 512 L.pjB 128 (Bh.getD i [])) := by
    unfold mlp
    exact f2_lin L.pjW 512 L.pjB 128 hhid
  have hoc := ho i hi'
  simp only [oCheck] at hoc
  unfold blockAt
  exact f2_sub (f2_vadd (f2_vadd (gx i) hatt) hmlp) _ hoc

/-- `layer_ok` for a prompt of 1 token. -/
theorem layer_ok1 (L : Layer) {xs : List (List ℝ)} {X0 Q0 A0 H0 O0 : List Iv}
    (hx : List.Forall₂ (List.Forall₂ (memAt S)) xs [X0])
    (q0 : qCheck L X0 Q0 = true)
    (a0 : aCheck L 0 [Q0] A0 = true)
    (h0 : hCheck L X0 H0 = true)
    (o0 : oCheck L X0 A0 H0 O0 = true) :
    List.Forall₂ (List.Forall₂ (memAt S)) (block L xs) [O0] := by
  refine layer_ok L (Bq := [Q0]) (Ba := [A0]) (Bh := [H0]) hx rfl rfl ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i < 1 := hi
    interval_cases i
    · exact q0
  · intro i hi
    have hi' : i < 1 := hi
    interval_cases i
    · exact a0
  · intro i hi
    have hi' : i < 1 := hi
    interval_cases i
    · exact h0
  · intro i hi
    have hi' : i < 1 := hi
    interval_cases i
    · exact o0

/-- `layer_ok` for a prompt of 3 tokens. -/
theorem layer_ok3 (L : Layer) {xs : List (List ℝ)} {X0 X1 X2 Q0 Q1 Q2 A0 A1 A2 H0 H1 H2 O0 O1 O2 : List Iv}
    (hx : List.Forall₂ (List.Forall₂ (memAt S)) xs [X0, X1, X2])
    (q0 : qCheck L X0 Q0 = true)
    (q1 : qCheck L X1 Q1 = true)
    (q2 : qCheck L X2 Q2 = true)
    (a0 : aCheck L 0 [Q0] A0 = true)
    (a1 : aCheck L 1 [Q0, Q1] A1 = true)
    (a2 : aCheck L 2 [Q0, Q1, Q2] A2 = true)
    (h0 : hCheck L X0 H0 = true)
    (h1 : hCheck L X1 H1 = true)
    (h2 : hCheck L X2 H2 = true)
    (o0 : oCheck L X0 A0 H0 O0 = true)
    (o1 : oCheck L X1 A1 H1 O1 = true)
    (o2 : oCheck L X2 A2 H2 O2 = true) :
    List.Forall₂ (List.Forall₂ (memAt S)) (block L xs) [O0, O1, O2] := by
  refine layer_ok L (Bq := [Q0, Q1, Q2]) (Ba := [A0, A1, A2]) (Bh := [H0, H1, H2]) hx rfl rfl ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i < 3 := hi
    interval_cases i
    · exact q0
    · exact q1
    · exact q2
  · intro i hi
    have hi' : i < 3 := hi
    interval_cases i
    · exact a0
    · exact a1
    · exact a2
  · intro i hi
    have hi' : i < 3 := hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro i hi
    have hi' : i < 3 := hi
    interval_cases i
    · exact o0
    · exact o1
    · exact o2

/-- `layer_ok` for a prompt of 5 tokens. -/
theorem layer_ok5 (L : Layer) {xs : List (List ℝ)} {X0 X1 X2 X3 X4 Q0 Q1 Q2 Q3 Q4 A0 A1 A2 A3 A4 H0 H1 H2 H3 H4 O0 O1 O2 O3 O4 : List Iv}
    (hx : List.Forall₂ (List.Forall₂ (memAt S)) xs [X0, X1, X2, X3, X4])
    (q0 : qCheck L X0 Q0 = true)
    (q1 : qCheck L X1 Q1 = true)
    (q2 : qCheck L X2 Q2 = true)
    (q3 : qCheck L X3 Q3 = true)
    (q4 : qCheck L X4 Q4 = true)
    (a0 : aCheck L 0 [Q0] A0 = true)
    (a1 : aCheck L 1 [Q0, Q1] A1 = true)
    (a2 : aCheck L 2 [Q0, Q1, Q2] A2 = true)
    (a3 : aCheck L 3 [Q0, Q1, Q2, Q3] A3 = true)
    (a4 : aCheck L 4 [Q0, Q1, Q2, Q3, Q4] A4 = true)
    (h0 : hCheck L X0 H0 = true)
    (h1 : hCheck L X1 H1 = true)
    (h2 : hCheck L X2 H2 = true)
    (h3 : hCheck L X3 H3 = true)
    (h4 : hCheck L X4 H4 = true)
    (o0 : oCheck L X0 A0 H0 O0 = true)
    (o1 : oCheck L X1 A1 H1 O1 = true)
    (o2 : oCheck L X2 A2 H2 O2 = true)
    (o3 : oCheck L X3 A3 H3 O3 = true)
    (o4 : oCheck L X4 A4 H4 O4 = true) :
    List.Forall₂ (List.Forall₂ (memAt S)) (block L xs) [O0, O1, O2, O3, O4] := by
  refine layer_ok L (Bq := [Q0, Q1, Q2, Q3, Q4]) (Ba := [A0, A1, A2, A3, A4]) (Bh := [H0, H1, H2, H3, H4]) hx rfl rfl ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i < 5 := hi
    interval_cases i
    · exact q0
    · exact q1
    · exact q2
    · exact q3
    · exact q4
  · intro i hi
    have hi' : i < 5 := hi
    interval_cases i
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact a4
  · intro i hi
    have hi' : i < 5 := hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · intro i hi
    have hi' : i < 5 := hi
    interval_cases i
    · exact o0
    · exact o1
    · exact o2
    · exact o3
    · exact o4

theorem layers_eq : layers = [LL 0, LL 1, LL 2, LL 3, LL 4, LL 5] := rfl

theorem foldl_layers (x0 : List (List ℝ)) :
    layers.foldl (fun xs L => block L xs) x0 =
      block (LL 5) (block (LL 4) (block (LL 3) (block (LL 2) (block (LL 1) (block (LL 0) x0))))) := by
  rw [layers_eq]
  simp only [List.foldl_cons, List.foldl_nil]

/-- An enclosure of `p x` from checked boxes of the residual vectors after the last layer. -/
theorem p_encl_of_boxes {x : List Bool} {B6 : List (List Iv)} {a b : ℤ}
    (h6 : List.Forall₂ (List.Forall₂ (memAt S))
      (layers.foldl (fun xs L => block L xs) ((enc x).map fun t => vec (embRow t) 128)) B6)
    (hc : pCheck B6 a b = true) : (a : ℝ) / 10 ^ 10 ≤ p x ∧ p x ≤ (b : ℝ) / 10 ^ 10 := by
  have hm : memAt S (p x) (pBox B6) := by
    have hp := memAt_recip (memAt_add memAt_one (memAt_exp (memAt_neg (memAt_final h6))))
    rw [← one_div] at hp
    exact hp
  simp only [pCheck, stIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hok, h1⟩, h2⟩ := hc
  exact encl_of_check hm hok h1 h2

end PRO
