import Mathlib
import CE.Model

/-! # Length-blindness on constant prompts

Rotary position embeddings enter only through the attention scores. On a prompt that repeats one
token, all positions carry the same residual stream, every head averages equal value vectors with
weights that sum to one, and so the hidden state at the last position does not depend on the length
of the prompt. This holds for every parameter assignment. -/

namespace CE

theorem zipWith_replicate_right {α β γ : Type*} (f : α → β → γ) (b : β) :
    ∀ l : List α, List.zipWith f l (List.replicate l.length b) = l.map fun a => f a b
  | [] => rfl
  | a :: l => by
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.map_cons,
      zipWith_replicate_right f b l]

theorem sum_map_mul_const (c : ℝ) : ∀ l : List ℝ, (l.map fun w => w * c).sum = l.sum * c
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_mul_const c l, add_mul]

theorem sum_map_exp_div (Z : ℝ) :
    ∀ l : List ℝ, (l.map fun x => Real.exp x / Z).sum = (l.map Real.exp).sum / Z
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_exp_div Z l, add_div]

theorem sum_exp_nonneg : ∀ l : List ℝ, 0 ≤ (l.map Real.exp).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := Real.exp_pos a
    have h2 := sum_exp_nonneg l
    linarith

theorem sum_exp_pos : ∀ l : List ℝ, 0 < l.length → 0 < (l.map Real.exp).sum
  | [], h => by simp at h
  | a :: l, _ => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := Real.exp_pos a
    have h2 := sum_exp_nonneg l
    linarith

/-- Softmax weights sum to one. -/
theorem softmax_sum (s : List ℝ) (h : 0 < s.length) : (softmax s).sum = 1 := by
  unfold softmax
  rw [sum_map_exp_div]
  exact div_self (sum_exp_pos s h).ne'

/-- Mixing equal value vectors with weights that sum to one returns that vector's coordinates. -/
theorem mix_const (ws : List ℝ) (v : List ℝ) (n : ℕ) (hl : ws.length = n) (hs : ws.sum = 1) :
    mix ws (List.replicate n v) = (List.range 32).map fun d => v.getD d 0 := by
  subst hl
  unfold mix
  apply List.map_congr_left
  intro d _
  simp only [zipWith_replicate_right, sum_map_mul_const, hs, one_mul]

theorem headOut_const (L : Layer) (u : List ℝ) (T j h : ℕ) (hj : j < T) :
    headOut L (List.replicate T u) j h =
      (List.range 32).map fun d => (((qkv L u).drop (96 * h + 64)).take 32).getD d 0 := by
  have htake : (List.replicate T u).take (j + 1) = List.replicate (j + 1) u := by
    rw [List.take_replicate, Nat.min_eq_left (by omega)]
  simp only [headOut, htake, List.map_replicate]
  apply mix_const
  · simp [softmax]
  · apply softmax_sum
    simp

/-- The attention output on equal inputs: the value vectors pushed through `attention.dense`. -/
noncomputable def attnC (L : Layer) (u : List ℝ) : List ℝ :=
  vadd (mv L.oW ((List.range 4).flatMap fun h =>
    (List.range 32).map fun d => (((qkv L u).drop (96 * h + 64)).take 32).getD d 0)) L.oB

theorem attnOut_const (L : Layer) (u : List ℝ) (T j : ℕ) (hj : j < T) :
    attnOut L (List.replicate T u) j = attnC L u := by
  have key : ∀ h, headOut L (List.replicate T u) j h =
      (List.range 32).map fun d => (((qkv L u).drop (96 * h + 64)).take 32).getD d 0 :=
    fun h => headOut_const L u T j h hj
  simp only [attnOut, attnC, key]

/-- One layer acting on a single residual stream shared by all positions. -/
noncomputable def stepC (L : Layer) (x : List ℝ) : List ℝ :=
  vadd (vadd x (attnC L (layerNorm L.ln1g L.ln1b x))) (mlpOut L (layerNorm L.ln2g L.ln2b x))

theorem map_range_const {α : Type*} (T : ℕ) (f : ℕ → α) (c : α) (h : ∀ j, j < T → f j = c) :
    (List.range T).map f = List.replicate T c := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h i (by simpa using h1)

theorem layer_const (L : Layer) (x : List ℝ) (T : ℕ) :
    layer L (List.replicate T x) = List.replicate T (stepC L x) := by
  unfold layer
  rw [List.length_replicate, List.map_replicate]
  apply map_range_const
  intro j hj
  rw [List.getD_replicate _ hj, attnOut_const L _ T j hj]
  rfl

theorem foldl_layer_const (Ls : List Layer) : ∀ (x : List ℝ) (T : ℕ),
    Ls.foldl (fun H L => layer L H) (List.replicate T x) =
      List.replicate T (Ls.foldl (fun y L => stepC L y) x) := by
  induction Ls with
  | nil => intro x T; rfl
  | cons L Ls ih =>
    intro x T
    simp only [List.foldl_cons]
    rw [layer_const, ih]

/-- **Length-blindness.** On a prompt that repeats one token `n ≥ 1` times, the final hidden state at
the last position is the one of the single-token prompt. -/
theorem lastHidden_replicate (θ : Params) (t n : ℕ) (hn : 1 ≤ n) :
    lastHidden θ (List.replicate n t) = lastHidden θ [t] := by
  have h1 : ∀ m : ℕ, 1 ≤ m → lastHidden θ (List.replicate m t) =
      layerNorm θ.lnfg θ.lnfb (θ.layers.foldl (fun y L => stepC L y) (θ.emb t)) := by
    intro m hm
    unfold lastHidden hidden
    rw [List.map_replicate, foldl_layer_const, List.length_replicate, List.getD_replicate _ (by omega)]
  rw [h1 n hn]
  exact (h1 1 le_rfl).symm

end CE
