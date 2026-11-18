import Mathlib
import CE.Model

/-! # Definitions for `collapse` and `eternal`

`Params`, `logit` are the exact real GPT-NeoX forward pass of `CE.Model` (pythia-14m's shape). -/

namespace CE

noncomputable section

/-- Tokens are natural numbers; the vocabulary is `0, …, vocab - 1`. -/
abbrev Token := ℕ

/-- Size of pythia-14m's unembedding. -/
def vocab : ℕ := 50304

/-- The next-token logits after the prompt `toks`, as a function of the candidate token. -/
def nextLogits (θ : Params) (toks : List Token) : Token → ℝ := fun t => logit θ toks t

/-- `some t` when `t` is a vocabulary token whose value is strictly larger than that of every other
vocabulary token; `none` when there is no such token. -/
def strictArgmax (v : Token → ℝ) : Option Token :=
  if h : ∃ t, t < vocab ∧ ∀ s, s < vocab → s ≠ t → v s < v t then some (Classical.choose h) else none

/-- Greedy choice: the first vocabulary token of largest value. -/
def argmax (v : Token → ℝ) : Token := ((List.range vocab).argmax v).getD 0

/-- Greedy decoding: the prompt `p` followed by `k` greedily chosen tokens. -/
def greedy (θ : Params) (p : List Token) : ℕ → List Token
  | 0 => p
  | k + 1 => greedy θ p k ++ [argmax (nextLogits θ (greedy θ p k))]

end

end CE
