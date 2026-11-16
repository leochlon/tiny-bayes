import Mathlib
import CE.Spec
import CE.Invariance

/-! # Collapse and eternal repetition

* `collapse`: on a prompt that repeats one token, the next-token logits are those of the one-token
  prompt, for every parameter assignment.
* `eternal`: if a token is the strict argmax of its own one-token prompt, greedy decoding from it
  repeats it forever. -/

namespace CE

/-- A strict argmax is the greedy choice. -/
theorem argmax_of_strict (v : Token → ℝ) (t : Token) (h : strictArgmax v = some t) : argmax v = t := by
  unfold strictArgmax at h
  by_cases hex : ∃ t, t < vocab ∧ ∀ s, s < vocab → s ≠ t → v s < v t
  · rw [dif_pos hex] at h
    have ht : Classical.choose hex = t := Option.some.inj h
    have hspec := Classical.choose_spec hex
    rw [ht] at hspec
    obtain ⟨hlt, hmax⟩ := hspec
    have hmem : t ∈ List.range vocab := List.mem_range.mpr hlt
    have harg : (List.range vocab).argmax v = some t := by
      rw [List.argmax_eq_some_iff]
      refine ⟨hmem, ?_, ?_⟩
      · intro a ha
        by_cases hat : a = t
        · rw [hat]
        · exact (hmax a (List.mem_range.mp ha) hat).le
      · intro a ha hle
        by_cases hat : a = t
        · rw [hat]
        · exact absurd (hmax a (List.mem_range.mp ha) hat) (not_lt.mpr hle)
    unfold argmax
    rw [harg]
    rfl
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

theorem collapse (θ : Params) (t : Token) (n : ℕ) (hn : 0 < n) :
    nextLogits θ (List.replicate n t) = nextLogits θ [t] := by
  funext s
  show dot (θ.unemb s) (lastHidden θ (List.replicate n t)) = dot (θ.unemb s) (lastHidden θ [t])
  rw [lastHidden_replicate θ t n hn]

theorem eternal (θ : Params) (t : Token) (ht : strictArgmax (nextLogits θ [t]) = t) (k : ℕ) :
    greedy θ [t] k = List.replicate (k + 1) t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hc : nextLogits θ (List.replicate (k + 1) t) = nextLogits θ [t] :=
      collapse θ t (k + 1) (Nat.succ_pos k)
    show greedy θ [t] k ++ [argmax (nextLogits θ (greedy θ [t] k))] = List.replicate (k + 1 + 1) t
    rw [ih, hc, argmax_of_strict _ t ht]
    exact (List.replicate_succ' (n := k + 1) (a := t)).symm

end CE
