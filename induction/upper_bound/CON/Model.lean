import Mathlib

/-! # The GPT-NeoX forward pass over the reals

`lastHidden θ toks` is the final hidden state (after the final LayerNorm) at the last position of the
token sequence `toks`, for a network of pythia-14m's shape with parameters `θ`: width 128, 4 heads of
width 32 (the `query_key_value` output is split per head into query, key, value of 32 coordinates
each), rotary position embeddings on the first 8 coordinates of each head (angles
`pos * 10000^(-i/4) = pos / 10^i`, `i = 0..3`), causal softmax attention with scores `q . k / sqrt 32`,
attention and MLP in parallel (`x + attn (ln1 x) + mlp (ln2 x)`), exact GELU `x * Phi x`, LayerNorm
with biased variance and `eps = 1e-5`, untied unembedding without bias. Every operation is the exact
real one (`Real.exp`, `Real.sqrt`, `Real.cos`, `Real.sin`, an integral for `Phi`). -/

namespace CON

noncomputable section

/-- Dot product of two real vectors. -/
def dot (x y : List ℝ) : ℝ := (List.zipWith (· * ·) x y).sum

/-- Matrix (list of rows) times vector. -/
def mv (W : List (List ℝ)) (x : List ℝ) : List ℝ := W.map fun row => dot row x

/-- Componentwise sum. -/
def vadd (x y : List ℝ) : List ℝ := List.zipWith (· + ·) x y

/-- LayerNorm with gain `g`, bias `b`: `g * (x - mean) / sqrt (var + 1e-5) + b`, biased variance. -/
def layerNorm (g b x : List ℝ) : List ℝ :=
  let d : ℝ := x.length
  let μ := x.sum / d
  let var := (x.map fun a => (a - μ) ^ 2).sum / d
  let s := Real.sqrt (var + 1 / 100000)
  vadd (List.zipWith (fun gi a => gi * ((a - μ) / s)) g x) b

/-- Standard normal distribution function `Phi x = 1/2 + (1 / sqrt (2 pi)) ∫_0^x exp (-t^2/2) dt`. -/
def Phi (x : ℝ) : ℝ :=
  1 / 2 + (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2) / 2)) / Real.sqrt (2 * Real.pi)

/-- Exact GELU. -/
def gelu (x : ℝ) : ℝ := x * Phi x

/-- Rotary embedding of a head vector at position `m`: coordinates `d < 8` are rotated in the pairs
`(d, d + 4)` by the angle `m / 10^d` (`d < 4`); the other coordinates pass through.
(`q * cos + rotate_half q * sin` with `rotate_half (x1, x2) = (-x2, x1)`.) -/
def rotary (m : ℕ) (x : List ℝ) : List ℝ :=
  (List.range x.length).map fun d =>
    if d < 4 then
      x.getD d 0 * Real.cos ((m : ℝ) / 10 ^ d) - x.getD (d + 4) 0 * Real.sin ((m : ℝ) / 10 ^ d)
    else if d < 8 then
      x.getD d 0 * Real.cos ((m : ℝ) / 10 ^ (d - 4)) + x.getD (d - 4) 0 * Real.sin ((m : ℝ) / 10 ^ (d - 4))
    else x.getD d 0

/-- Softmax of a list of scores. -/
def softmax (s : List ℝ) : List ℝ := s.map fun x => Real.exp x / (s.map Real.exp).sum

/-- Attention-weighted sum of the value vectors (32 coordinates). -/
def mix (ws : List ℝ) (vs : List (List ℝ)) : List ℝ :=
  (List.range 32).map fun d => (List.zipWith (fun w v => w * v.getD d 0) ws vs).sum

/-- The parameters of one layer (matrices as lists of rows, `out × in`). -/
structure Layer where
  ln1g : List ℝ
  ln1b : List ℝ
  ln2g : List ℝ
  ln2b : List ℝ
  /-- `attention.query_key_value.weight`, 384 × 128 -/
  qkvW : List (List ℝ)
  qkvB : List ℝ
  /-- `attention.dense.weight`, 128 × 128 -/
  oW : List (List ℝ)
  oB : List ℝ
  /-- `mlp.dense_h_to_4h.weight`, 512 × 128 -/
  fW : List (List ℝ)
  fB : List ℝ
  /-- `mlp.dense_4h_to_h.weight`, 128 × 512 -/
  pW : List (List ℝ)
  pB : List ℝ

/-- All parameters: input embedding rows, layers, final LayerNorm, unembedding rows. -/
structure Params where
  emb : ℕ → List ℝ
  layers : List Layer
  lnfg : List ℝ
  lnfb : List ℝ
  unemb : ℕ → List ℝ

/-- `query_key_value` applied to one (layer-normed) position: 384 coordinates, for head `h` the
query is `[96 h, 96 h + 32)`, the key `[96 h + 32, 96 h + 64)`, the value `[96 h + 64, 96 h + 96)`. -/
def qkv (L : Layer) (u : List ℝ) : List ℝ := vadd (mv L.qkvW u) L.qkvB

/-- Output of head `h` at position `j`; `U` holds the layer-normed inputs of all positions. Position
`j` attends to the positions `0..j`. -/
def headOut (L : Layer) (U : List (List ℝ)) (j h : ℕ) : List ℝ :=
  let vis := U.take (j + 1)
  let q := rotary j (((qkv L (U.getD j [])).drop (96 * h)).take 32)
  let ks := List.zipWith (fun i u => rotary i (((qkv L u).drop (96 * h + 32)).take 32)) (List.range (j + 1)) vis
  let vs := vis.map fun u => ((qkv L u).drop (96 * h + 64)).take 32
  let ws := softmax (ks.map fun k => dot q k / Real.sqrt 32)
  mix ws vs

/-- Attention output at position `j`: the four heads concatenated, then `attention.dense`. -/
def attnOut (L : Layer) (U : List (List ℝ)) (j : ℕ) : List ℝ :=
  vadd (mv L.oW ((List.range 4).flatMap fun h => headOut L U j h)) L.oB

/-- MLP output for one (layer-normed) position. -/
def mlpOut (L : Layer) (u : List ℝ) : List ℝ :=
  vadd (mv L.pW ((vadd (mv L.fW u) L.fB).map gelu)) L.pB

/-- One layer with parallel residual: `x + attn (ln1 x) + mlp (ln2 x)` at every position. -/
def layer (L : Layer) (H : List (List ℝ)) : List (List ℝ) :=
  (List.range H.length).map fun j =>
    vadd (vadd (H.getD j []) (attnOut L (H.map (layerNorm L.ln1g L.ln1b)) j))
      (mlpOut L (layerNorm L.ln2g L.ln2b (H.getD j [])))

/-- Residual streams of all positions after the last layer. -/
def hidden (θ : Params) (toks : List ℕ) : List (List ℝ) :=
  θ.layers.foldl (fun H L => layer L H) (toks.map θ.emb)

/-- Final hidden state at the last position, after the final LayerNorm. -/
def lastHidden (θ : Params) (toks : List ℕ) : List ℝ :=
  layerNorm θ.lnfg θ.lnfb ((hidden θ toks).getD (toks.length - 1) [])

/-- Logit of the next token `t` after the prompt `toks`. -/
def logit (θ : Params) (toks : List ℕ) (t : ℕ) : ℝ := dot (θ.unemb t) (lastHidden θ toks)

end

end CON
