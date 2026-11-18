import Mathlib
import CON.Model
import CON.F16
import CON.W.L0
import CON.W.L1
import CON.W.L2
import CON.W.L3
import CON.W.L4
import CON.W.L5
import CON.W.Fin
import CON.W.EIndex
import CON.W.UIndex

/-! # pythia-14m

`pythia14m : Params` holds all 14,067,712 parameters of EleutherAI/pythia-14m (main branch), read from
`model.safetensors` as float16 bit patterns (`CON.W.*`) and decoded exactly: the parameter with bit
pattern `b` is the real number `f16num b / 2^24`.

* `input_layernorm` is `ln1` (before attention), `post_attention_layernorm` is `ln2` (before the MLP);
* `emb t` is row `t` of `gpt_neox.embed_in.weight`, `unemb t` is row `t` of `embed_out.weight`
  (tokens `t ≥ 50304` do not exist; their rows decode to zeros). -/

namespace CON

noncomputable section

/-- The real value of the float16 with bit pattern `b`. -/
def f16 (b : ℕ) : ℝ := (f16num b : ℝ) / 2 ^ 24

/-- A packed row of `m` float16 entries as a real vector. -/
def row (m r : ℕ) : List ℝ := (List.range m).map fun j => f16 (field r j)

/-- A matrix with `m` columns from its packed rows. -/
def mat (m : ℕ) (rs : List ℕ) : List (List ℝ) := rs.map (row m)

/-- Layer 0 (`gpt_neox.layers.0`). -/
def layer0 : Layer where
  ln1g := row 128 W.L0.ln1g
  ln1b := row 128 W.L0.ln1b
  ln2g := row 128 W.L0.ln2g
  ln2b := row 128 W.L0.ln2b
  qkvW := mat 128 W.L0.qkvW
  qkvB := row 384 W.L0.qkvB
  oW := mat 128 W.L0.oW
  oB := row 128 W.L0.oB
  fW := mat 128 W.L0.fW
  fB := row 512 W.L0.fB
  pW := mat 512 W.L0.pW
  pB := row 128 W.L0.pB

/-- Layer 1 (`gpt_neox.layers.1`). -/
def layer1 : Layer where
  ln1g := row 128 W.L1.ln1g
  ln1b := row 128 W.L1.ln1b
  ln2g := row 128 W.L1.ln2g
  ln2b := row 128 W.L1.ln2b
  qkvW := mat 128 W.L1.qkvW
  qkvB := row 384 W.L1.qkvB
  oW := mat 128 W.L1.oW
  oB := row 128 W.L1.oB
  fW := mat 128 W.L1.fW
  fB := row 512 W.L1.fB
  pW := mat 512 W.L1.pW
  pB := row 128 W.L1.pB

/-- Layer 2 (`gpt_neox.layers.2`). -/
def layer2 : Layer where
  ln1g := row 128 W.L2.ln1g
  ln1b := row 128 W.L2.ln1b
  ln2g := row 128 W.L2.ln2g
  ln2b := row 128 W.L2.ln2b
  qkvW := mat 128 W.L2.qkvW
  qkvB := row 384 W.L2.qkvB
  oW := mat 128 W.L2.oW
  oB := row 128 W.L2.oB
  fW := mat 128 W.L2.fW
  fB := row 512 W.L2.fB
  pW := mat 512 W.L2.pW
  pB := row 128 W.L2.pB

/-- Layer 3 (`gpt_neox.layers.3`). -/
def layer3 : Layer where
  ln1g := row 128 W.L3.ln1g
  ln1b := row 128 W.L3.ln1b
  ln2g := row 128 W.L3.ln2g
  ln2b := row 128 W.L3.ln2b
  qkvW := mat 128 W.L3.qkvW
  qkvB := row 384 W.L3.qkvB
  oW := mat 128 W.L3.oW
  oB := row 128 W.L3.oB
  fW := mat 128 W.L3.fW
  fB := row 512 W.L3.fB
  pW := mat 512 W.L3.pW
  pB := row 128 W.L3.pB

/-- Layer 4 (`gpt_neox.layers.4`). -/
def layer4 : Layer where
  ln1g := row 128 W.L4.ln1g
  ln1b := row 128 W.L4.ln1b
  ln2g := row 128 W.L4.ln2g
  ln2b := row 128 W.L4.ln2b
  qkvW := mat 128 W.L4.qkvW
  qkvB := row 384 W.L4.qkvB
  oW := mat 128 W.L4.oW
  oB := row 128 W.L4.oB
  fW := mat 128 W.L4.fW
  fB := row 512 W.L4.fB
  pW := mat 512 W.L4.pW
  pB := row 128 W.L4.pB

/-- Layer 5 (`gpt_neox.layers.5`). -/
def layer5 : Layer where
  ln1g := row 128 W.L5.ln1g
  ln1b := row 128 W.L5.ln1b
  ln2g := row 128 W.L5.ln2g
  ln2b := row 128 W.L5.ln2b
  qkvW := mat 128 W.L5.qkvW
  qkvB := row 384 W.L5.qkvB
  oW := mat 128 W.L5.oW
  oB := row 128 W.L5.oB
  fW := mat 128 W.L5.fW
  fB := row 512 W.L5.fB
  pW := mat 512 W.L5.pW
  pB := row 128 W.L5.pB

/-- EleutherAI/pythia-14m, all parameters. -/
def pythia14m : Params where
  emb := fun t => row 128 ((W.eChunks.getD (t / 256) []).getD (t % 256) 0)
  layers := [layer0, layer1, layer2, layer3, layer4, layer5]
  lnfg := row 128 W.lnfg
  lnfb := row 128 W.lnfb
  unemb := fun t => row 128 ((W.uChunks.getD (t / 256) []).getD (t % 256) 0)

end

end CON
