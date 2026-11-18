import Mathlib
import CON.PRO.Act
import CON.PRO.Bits.E
import CON.PRO.Bits.L0
import CON.PRO.Bits.L1
import CON.PRO.Bits.L2
import CON.PRO.Bits.L3
import CON.PRO.Bits.L4
import CON.PRO.Bits.L5

/-! # Pythia-14M as a real function

EleutherAI/pythia-14m (GPT-NeoX, main checkpoint, revision cf967c0a) over `ℝ`, following the
Hugging Face implementation `GPTNeoXForCausalLM` operation by operation:

    x_j = embed_in[tok_j]
    six times:  x_j <- x_j + attn (ln1 x)_j + mlp (ln2 x_j)            (attention and MLP in parallel)
    attn: qkv = W_qkv h + b_qkv; head h reads q, k, v from qkv[96h .. 96h+96); the first 8 of the 32
          dimensions of q and k are rotated by the angles m * 10^(-f), f = 0..3, m = position;
          weights = softmax_j (q_i . k_j / sqrt 32) over j <= i; heads concatenated; then W_d, b_d
    mlp:  W_pj (gelu (W_fc h + b_fc)) + b_pj,  gelu x = x * Phi x  (exact GELU)
    ln:   g * (x - mean) / sqrt (var + 1e-5) + b                        (biased variance over 128)
    logits = embed_out (ln_f x_last)

Every weight is the exact dyadic rational of its float16 bit pattern (`PRO.Bits`); nothing is rounded.
Only the embedding rows of the four prompt tokens and the unembedding rows of the two candidate
tokens are included; no other embedding row enters the outputs defined here. -/

namespace CON.PRO

noncomputable section

/-- Numerator over `2^24` of the IEEE-754 binary16 number with bit pattern `b` (finite patterns):
sign `b / 2^15`, exponent field `e = b / 2^10 mod 32`, fraction `m = b mod 2^10`; the value is
`± m * 2^-24` if `e = 0` and `± (1024 + m) * 2^(e - 25)` otherwise. -/
def f16num (b : ℕ) : ℤ :=
  let m := b % 1024
  let e := (b / 1024) % 32
  let mag : ℕ := if e = 0 then m else (1024 + m) * 2 ^ (e - 1)
  if (b / 32768) % 2 = 0 then (mag : ℤ) else -(mag : ℤ)

/-- Entry `i` of a packed float16 buffer, as a real number. -/
def ent (bits i : ℕ) : ℝ := (f16num ((bits >>> (16 * i)) % 65536) : ℝ) / 16777216

/-- The first `n` entries of a packed buffer. -/
def vec (bits n : ℕ) : List ℝ := (List.range n).map (ent bits)

/-- A matrix with `n` columns from its packed rows. -/
def mat (rows : List ℕ) (n : ℕ) : List (List ℝ) := rows.map fun r => vec r n

def dot (x y : List ℝ) : ℝ := (List.zipWith (· * ·) x y).sum

def vadd (x y : List ℝ) : List ℝ := List.zipWith (· + ·) x y

/-- `W x + b`. -/
def lin (W : List (List ℝ)) (b x : List ℝ) : List ℝ := vadd (W.map fun r => dot r x) b

/-- Mean over the 128 coordinates. -/
def lnMean (x : List ℝ) : ℝ := x.sum / 128

/-- `1 / sqrt (var + eps)`: biased variance over the 128 coordinates, `eps = 1e-5`. -/
def lnInvStd (x : List ℝ) : ℝ :=
  (Real.sqrt ((x.map fun t => (t - lnMean x) ^ 2).sum / 128 + 1 / 100000))⁻¹

/-- LayerNorm: `g * (x - mean) / sqrt (var + eps) + b`. -/
def layerNorm (g b x : List ℝ) : List ℝ :=
  vadd (List.zipWith (fun gi t => gi * ((t - lnMean x) * lnInvStd x)) g x) b

/-- The packed weights of one layer. -/
structure Layer where
  ln1g : ℕ
  ln1b : ℕ
  qkvW : List ℕ
  qkvB : ℕ
  dW : List ℕ
  dB : ℕ
  ln2g : ℕ
  ln2b : ℕ
  fcW : List ℕ
  fcB : ℕ
  pjW : List ℕ
  pjB : ℕ

def layers : List Layer := [
  ⟨Bits.L0.ln1g, Bits.L0.ln1b, Bits.L0.qkvW, Bits.L0.qkvB, Bits.L0.dW, Bits.L0.dB,
    Bits.L0.ln2g, Bits.L0.ln2b, Bits.L0.fcW, Bits.L0.fcB, Bits.L0.pjW, Bits.L0.pjB⟩,
  ⟨Bits.L1.ln1g, Bits.L1.ln1b, Bits.L1.qkvW, Bits.L1.qkvB, Bits.L1.dW, Bits.L1.dB,
    Bits.L1.ln2g, Bits.L1.ln2b, Bits.L1.fcW, Bits.L1.fcB, Bits.L1.pjW, Bits.L1.pjB⟩,
  ⟨Bits.L2.ln1g, Bits.L2.ln1b, Bits.L2.qkvW, Bits.L2.qkvB, Bits.L2.dW, Bits.L2.dB,
    Bits.L2.ln2g, Bits.L2.ln2b, Bits.L2.fcW, Bits.L2.fcB, Bits.L2.pjW, Bits.L2.pjB⟩,
  ⟨Bits.L3.ln1g, Bits.L3.ln1b, Bits.L3.qkvW, Bits.L3.qkvB, Bits.L3.dW, Bits.L3.dB,
    Bits.L3.ln2g, Bits.L3.ln2b, Bits.L3.fcW, Bits.L3.fcB, Bits.L3.pjW, Bits.L3.pjB⟩,
  ⟨Bits.L4.ln1g, Bits.L4.ln1b, Bits.L4.qkvW, Bits.L4.qkvB, Bits.L4.dW, Bits.L4.dB,
    Bits.L4.ln2g, Bits.L4.ln2b, Bits.L4.fcW, Bits.L4.fcB, Bits.L4.pjW, Bits.L4.pjB⟩,
  ⟨Bits.L5.ln1g, Bits.L5.ln1b, Bits.L5.qkvW, Bits.L5.qkvB, Bits.L5.dW, Bits.L5.dB,
    Bits.L5.ln2g, Bits.L5.ln2b, Bits.L5.fcW, Bits.L5.fcB, Bits.L5.pjW, Bits.L5.pjB⟩]

/-- Rotary position embedding at position `m` on a head vector of 32 coordinates: coordinates
`(f, f + 4)`, `f < 4`, are rotated by the angle `m * 10^(-f)` (`10000^(-2f/8) = 10^(-f)`); the other
24 coordinates are unchanged. -/
def rot (m : ℕ) (u : List ℝ) : List ℝ :=
  (List.range 32).map fun i =>
    if i < 4 then
      u.getD i 0 * Real.cos ((m : ℝ) / (10 : ℝ) ^ i) - u.getD (i + 4) 0 * Real.sin ((m : ℝ) / (10 : ℝ) ^ i)
    else if i < 8 then
      u.getD i 0 * Real.cos ((m : ℝ) / (10 : ℝ) ^ (i - 4)) +
        u.getD (i - 4) 0 * Real.sin ((m : ℝ) / (10 : ℝ) ^ (i - 4))
    else u.getD i 0

/-- Coordinates `a .. a + n - 1` of a vector. -/
def slice (u : List ℝ) (a n : ℕ) : List ℝ := (u.drop a).take n

/-- Softmax of a list of scores. -/
def softmax (s : List ℝ) : List ℝ := (s.map Real.exp).map fun e => e / (s.map Real.exp).sum

/-- Output of head `h` at position `i`, from the `qkv` vectors of positions `0 .. i`: the query is
read at position `i`, keys and values at positions `j ≤ i`, scores are `q . k / sqrt 32`. -/
def headOut (i : ℕ) (qkvs : List (List ℝ)) (h : ℕ) : List ℝ :=
  (List.range 32).map fun d =>
    (List.zipWith (fun aj v => aj * v.getD d 0)
      (softmax ((List.range (i + 1)).map fun j =>
        dot (rot i (slice (qkvs.getD i []) (96 * h) 32))
          (rot j (slice (qkvs.getD j []) (96 * h + 32) 32)) * (Real.sqrt 32)⁻¹))
      (qkvs.map fun u => slice u (96 * h + 64) 32)).sum

/-- Attention output at position `i`, from the `qkv` vectors of positions `0 .. i`. -/
def attn (L : Layer) (i : ℕ) (qkvs : List (List ℝ)) : List ℝ :=
  lin (mat L.dW 128) (vec L.dB 128)
    (headOut i qkvs 0 ++ headOut i qkvs 1 ++ headOut i qkvs 2 ++ headOut i qkvs 3)

def mlp (L : Layer) (h : List ℝ) : List ℝ :=
  lin (mat L.pjW 512) (vec L.pjB 128) ((lin (mat L.fcW 128) (vec L.fcB 512) h).map gelu)

/-- One layer on the residual vectors of all positions (attention and MLP in parallel). -/
def block (L : Layer) (xs : List (List ℝ)) : List (List ℝ) :=
  (List.range xs.length).map fun i =>
    vadd (vadd (xs.getD i [])
        (attn L i ((xs.map fun x => lin (mat L.qkvW 128) (vec L.qkvB 384)
          (layerNorm (vec L.ln1g 128) (vec L.ln1b 128) x)).take (i + 1))))
      (mlp L (layerNorm (vec L.ln2g 128) (vec L.ln2b 128) (xs.getD i [])))

/-- Packed `embed_in` row of a token: `<|endoftext|>` (0), `,` (13), ` red` (2502), ` blue` (4797). -/
def embRow : ℕ → ℕ
  | 0 => Bits.E.in_bos
  | 13 => Bits.E.in_comma
  | 2502 => Bits.E.in_red
  | 4797 => Bits.E.in_blue
  | _ => 0

/-- `logit(" red") - logit(" blue")` read at the last position of the final residual vectors. -/
def final (xs : List (List ℝ)) : ℝ :=
  dot (vec Bits.E.out_red 128)
      (layerNorm (vec Bits.E.lnfg 128) (vec Bits.E.lnfb 128) (xs.getD (xs.length - 1) [])) -
    dot (vec Bits.E.out_blue 128)
      (layerNorm (vec Bits.E.lnfg 128) (vec Bits.E.lnfb 128) (xs.getD (xs.length - 1) []))

/-- `logit(" red") - logit(" blue")` for the next token after `toks`. -/
def logitDiff (toks : List ℕ) : ℝ :=
  final (layers.foldl (fun xs L => block L xs) (toks.map fun t => vec (embRow t) 128))

/-- ` red` (2502) for `true`, ` blue` (4797) for `false`. -/
def tokOf (b : Bool) : ℕ := if b then 2502 else 4797

/-- Each observation is followed by a comma (token 13). -/
def encBits : List Bool → List ℕ
  | [] => []
  | b :: bs => tokOf b :: 13 :: encBits bs

/-- The prompt of a binary sequence: `<|endoftext|>` (token 0), then the observations. -/
def enc (x : List Bool) : List ℕ := 0 :: encBits x

/-- Pythia-14M's probability that the next observation is ` red`, renormalised over ` red`, ` blue`. -/
def p (x : List Bool) : ℝ := 1 / (1 + Real.exp (-(logitDiff (enc x))))

end

end CON.PRO
