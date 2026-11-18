import PRO.Mirror

/-! Box checks for a certified forward pass, one position and one step at a time (core Lean only).

A box is a literal list of intervals. Each check runs one step of the interval forward pass of
`PRO.Mirror` on boxes and tests that the result lies inside the next box. `PRO.Compose` proves that
checked boxes enclose the real model. The four steps of a layer at position `i`:

* `qCheck`: LayerNorm 1 and `query_key_value`;
* `aCheck`: attention of position `i` over the `qkv` boxes of positions `0..i`, then `dense`;
* `hCheck`: LayerNorm 2, `dense_h_to_4h` and GELU;
* `oCheck`: input + attention output + `dense_4h_to_h` of the hidden box. -/

namespace PRO

/-- Every interval of the first list is valid and lies inside the box at the same place. -/
def allSub : List Iv → List Iv → Bool
  | [], [] => true
  | X :: Xs, B :: Bs => inB X B && allSub Xs Bs
  | [], _ :: _ => false
  | _ :: _, [] => false

/-- Layer `k` of the model. -/
def LL (k : Nat) : Layer := layers.getD k ⟨0, 0, [], 0, [], 0, 0, 0, [], 0, [], 0⟩

def qCheck (L : Layer) (Bx Bq : List Iv) : Bool :=
  stList (layerNormI L.ln1g L.ln1b Bx) fun H => allSub (linI L.qkvW 128 L.qkvB 384 H) Bq

def aCheck (L : Layer) (i : Nat) (Bqs : List (List Iv)) (Ba : List Iv) : Bool :=
  allSub (attnI L i Bqs) Ba

def hCheck (L : Layer) (Bx Bh : List Iv) : Bool :=
  stList (layerNormI L.ln2g L.ln2b Bx) fun H => allSub ((linI L.fcW 128 L.fcB 512 H).map geluI) Bh

def oCheck (L : Layer) (Bx Ba Bh Bo : List Iv) : Bool :=
  allSub (vaddI (vaddI Bx Ba) (linI L.pjW 512 L.pjB 128 Bh)) Bo

/-- Enclosure of the prediction from the boxes of the final residual vectors. -/
def pBox (B6 : List (List Iv)) : Iv := recip (add one (expI (neg (finalI B6))))

/-- Checks `a / 10^10 ≤ p ≤ b / 10^10` from the boxes of the final residual vectors. -/
def pCheck (B6 : List (List Iv)) (a b : Int) : Bool :=
  stIv (pBox B6) fun D => D.ok && decide (a * S ≤ D.lo * TEN10) && decide (D.hi * TEN10 ≤ b * S)

end PRO
