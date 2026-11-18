import PRO.Model
import PRO.Force
import PRO.Gelu
import PRO.Elem
import PRO.Trig

/-! The interval forward pass that the kernel evaluates. It mirrors `PRO.logitDiff` operation by
operation; `PRO.logitDiff_sound` (in `PRO.Sound`) proves that it encloses the real model. The
`st…` combinators of `PRO.Force` only fix the evaluation order (`stList_eq` etc.). -/

namespace PRO

/-- Integer numerator (over `2^24`) of entry `i` of a packed float16 buffer. -/
def numAt (bits i : Nat) : Int := f16num ((bits >>> (16 * i)) % 65536)

def rowNums (bits n : Nat) : List Int := (List.range n).map (numAt bits)

def vecI (bits n : Nat) : List Iv := (rowNums bits n).map ofW

/-- `W X + b` with exact weights. -/
def linI (rows : List Nat) (n bias m : Nat) (X : List Iv) : List Iv :=
  vaddI (rows.map fun r => dotWI (rowNums r n) X) (vecI bias m)

/-- `1e-5` at scale `S`. -/
def EPS : Iv := ⟨fdiv S 100000, cdiv S 100000, true⟩

def S128 : Int := S * 128

def layerNormI (g b : Nat) (X : List Iv) : List Iv :=
  stIv (downBy 128 (sumI X)) fun μ =>
  stIv (recip (sqrtI (add (downBy S128
      (sumI (X.map fun t => mulRaw (add t (neg μ)) (add t (neg μ))))) EPS))) fun r =>
  vaddI (List.zipWith (fun gi t => mul (ofW gi) (mul (add t (neg μ)) r)) (rowNums g 128) X) (vecI b 128)

def rotI (m : Nat) (U : List Iv) : List Iv :=
  (List.range 32).map fun i =>
    if i < 4 then add (mul (U.getD i zero) (cosT m i)) (neg (mul (U.getD (i + 4) zero) (sinT m i)))
    else if i < 8 then
      add (mul (U.getD i zero) (cosT m (i - 4))) (mul (U.getD (i - 4) zero) (sinT m (i - 4)))
    else U.getD i zero

def sliceI (U : List Iv) (a n : Nat) : List Iv := (U.drop a).take n

/-- Largest upper endpoint of a list of intervals. -/
def maxHi : List Iv → Int
  | [] => 0
  | [X] => X.hi
  | X :: Xs => max X.hi (maxHi Xs)

/-- Softmax, computed after subtracting the constant `maxHi / S` from every score. -/
def softmaxI (Sc : List Iv) : List Iv :=
  stInt (maxHi Sc) fun m =>
  stList (Sc.map fun s => expI (add s ⟨-m, -m, true⟩)) fun E =>
  stIv (recip (sumI E)) fun Zi =>
  E.map fun e => mul e Zi

def headOutI (i : Nat) (QKVs : List (List Iv)) (h : Nat) : List Iv :=
  stList (rotI i (sliceI (QKVs.getD i []) (96 * h) 32)) fun Q =>
  stIv (recip (sqrtI ⟨32 * S, 32 * S, true⟩)) fun rs =>
  stList ((List.range (i + 1)).map fun j =>
    mul (dotI Q (rotI j (sliceI (QKVs.getD j []) (96 * h + 32) 32))) rs) fun Sc =>
  stList (softmaxI Sc) fun A =>
  (List.range 32).map fun d =>
    downBy S (sumI (List.zipWith (fun aj v => mulRaw aj (v.getD d zero)) A
      (QKVs.map fun u => sliceI u (96 * h + 64) 32)))

def attnI (L : Layer) (i : Nat) (QKVs : List (List Iv)) : List Iv :=
  stList (headOutI i QKVs 0 ++ headOutI i QKVs 1 ++ headOutI i QKVs 2 ++ headOutI i QKVs 3) fun Hd =>
  linI L.dW 128 L.dB 128 Hd

def mlpI (L : Layer) (H : List Iv) : List Iv :=
  stList (linI L.fcW 128 L.fcB 512 H) fun A =>
  stList (A.map geluI) fun G =>
  linI L.pjW 512 L.pjB 128 G

def blockI (L : Layer) (Xs : List (List Iv)) : List (List Iv) :=
  stLL (Xs.map fun X => stList (layerNormI L.ln1g L.ln1b X) fun H =>
    linI L.qkvW 128 L.qkvB 384 H) fun QKVs =>
  (List.range Xs.length).map fun i =>
    vaddI (vaddI (Xs.getD i []) (attnI L i (QKVs.take (i + 1))))
      (stList (layerNormI L.ln2g L.ln2b (Xs.getD i [])) fun H2 => mlpI L H2)

def finalI (Xs : List (List Iv)) : Iv :=
  stList (layerNormI Bits.E.lnfg Bits.E.lnfb (Xs.getD (Xs.length - 1) [])) fun Y =>
  add (dotWI (rowNums Bits.E.out_red 128) Y) (neg (dotWI (rowNums Bits.E.out_blue 128) Y))

def runI : List Layer → List (List Iv) → Iv
  | [], Xs => finalI Xs
  | L :: Ls, Xs => stLL (blockI L Xs) fun Ys => runI Ls Ys

def logitDiffI (toks : List Nat) : Iv :=
  stLL (toks.map fun t => vecI (embRow t) 128) fun X0 => runI layers X0

/-- Interval enclosure of `p x`. -/
def pI (x : List Bool) : Iv := recip (add one (expI (neg (logitDiffI (enc x)))))

/-- `10^10`. -/
def TEN10 : Int := 10000000000

/-- Checks `a / 10^10 ≤ p x ≤ b / 10^10`. -/
def pointCheck (x : List Bool) (a b : Int) : Bool :=
  stIv (pI x) fun D => D.ok && decide (a * S ≤ D.lo * TEN10) && decide (D.hi * TEN10 ≤ b * S)

/-- All Boolean lists of length `n`. -/
def allLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allLists n).map (List.cons false) ++ (allLists n).map (List.cons true)

/-- The orderings of the bag `(n, k)`: lists of length `n` with exactly `k` entries `true`. -/
def orderings (n k : Nat) : List (List Bool) := (allLists n).filter fun l => decide (l.count true = k)

/-- Checks `a / 10^10 ≤ (1 / C) * Σ_{x ∈ orderings n k} p x ≤ b / 10^10`, `C` the number of orderings. -/
def bagCheck (n k : Nat) (a b : Int) : Bool :=
  stIv (sumI ((orderings n k).map pI)) fun T =>
    T.ok && decide (a * ((orderings n k).length : Int) * S ≤ T.lo * TEN10) &&
      decide (T.hi * TEN10 ≤ b * ((orderings n k).length : Int) * S)

/-- Checks `a / 10^10 ≤ p x - p x' ≤ b / 10^10`. -/
def gapCheck (x x' : List Bool) (a b : Int) : Bool :=
  stIv (add (pI x) (neg (pI x'))) fun D =>
    D.ok && decide (a * S ≤ D.lo * TEN10) && decide (D.hi * TEN10 ≤ b * S)

end PRO
