import Bridge
import Shard
import OutputData

namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bits (j : Nat) : Nat := (CON.W.uChunks.getD (j/256) []).getD (j%256) 0
def logitI (j : Nat) (H : List PRO.Iv) : PRO.Iv := PRO.dotWI (PRO.rowNums (bits j) 128) H
def centerRow (j : Nat) : Bool :=
  let J := logitI j center
  J.ok && decide (2*PRO.S ≤ reference.lo-J.hi)
def centerBlock (k : Nat) : Bool :=
  (List.range (min 256 (50304-k*256))).all fun i =>
    if k*256+i = 10166 then true else centerRow (k*256+i)

theorem reference_checked : PRO.inB (logitI 10166 center) reference = true := by decide +kernel
theorem reference_valid : reference.ok = true := by decide +kernel
theorem center_valid : ∀ B ∈ center, B.ok = true := by decide +kernel
theorem witness_valid : ∀ B ∈ witness, B.ok = true := by decide +kernel

theorem logit_mem {h : List ℝ} {H : List PRO.Iv}
    (hh : List.Forall₂ (PRO.memAt PRO.S) h H) (j : Nat) :
    PRO.memAt PRO.S (CON.dot (CON.pythia14m.unemb j) h) (logitI j H) := by
  change PRO.memAt PRO.S (CON.dot (CON.row 128 (bits j)) h) (logitI j H)
  rw [row_eq_vec, PRO.vec_eq]
  exact PRO.memAt_dotWI _ hh

theorem center_row_sound {h : List ℝ}
    (hh : List.Forall₂ (PRO.memAt PRO.S) h center) (j : Nat)
    (hc : centerRow j = true) :
    (2:ℝ) ≤ CON.dot (CON.pythia14m.unemb 10166) h - CON.dot (CON.pythia14m.unemb j) h := by
  have hy := (PRO.memAt_inB (logit_mem hh 10166) reference_checked) reference_valid
  simp only [centerRow, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hj := (logit_mem hh j) hc.1
  have hn : (2:ℝ)*PRO.S ≤ (reference.lo:ℝ) - (logitI j center).hi := by exact_mod_cast hc.2
  have hmul : (2:ℝ)*PRO.S ≤
      (CON.dot (CON.pythia14m.unemb 10166) h - CON.dot (CON.pythia14m.unemb j) h)*PRO.S := by
    nlinarith [hy.1,hj.2]
  nlinarith [PRO.S_pos]

theorem all_center_rows_of_blocks {h : List ℝ}
    (hh : List.Forall₂ (PRO.memAt PRO.S) h center)
    (hc : ∀ k, k < 197 → centerBlock k = true) :
    ∀ j : Fin 50304, j.val ≠ 10166 →
      (2:ℝ) ≤ CON.dot (CON.pythia14m.unemb 10166) h - CON.dot (CON.pythia14m.unemb j.val) h := by
  intro j hj
  have hblock := hc (j.val/256) (by omega)
  simp only [centerBlock, List.all_eq_true] at hblock
  have hin : j.val%256 ∈ List.range (min 256 (50304-(j.val/256)*256)) := by
    apply List.mem_range.mpr
    omega
  have h := hblock (j.val%256) hin
  have he : (j.val/256)*256+j.val%256 = j.val := by omega
  rw [he, if_neg hj] at h
  exact center_row_sound hh j.val h

def witnessGap : PRO.Iv := PRO.add (logitI 10895 witness) (PRO.neg (logitI 10166 witness))
theorem witness_checked : witnessGap.ok = true ∧ PRO.S ≤ 20*witnessGap.lo := by decide +kernel

theorem witness_gap_of_hidden {h : List ℝ}
    (hh : List.Forall₂ (PRO.memAt PRO.S) h witness) :
    (1/20:ℝ) ≤ CON.dot (CON.pythia14m.unemb 10895) h - CON.dot (CON.pythia14m.unemb 10166) h := by
  have hg := PRO.memAt_add (logit_mem hh 10895) (PRO.memAt_neg (logit_mem hh 10166))
  change PRO.memAt PRO.S (CON.dot (CON.pythia14m.unemb 10895) h - CON.dot (CON.pythia14m.unemb 10166) h) witnessGap at hg
  have hb := hg witness_checked.1
  have hn : (PRO.S:ℝ) ≤ 20*(witnessGap.lo:ℝ) := by exact_mod_cast witness_checked.2
  have hmul : (1/20:ℝ)*PRO.S ≤
      (CON.dot (CON.pythia14m.unemb 10895) h - CON.dot (CON.pythia14m.unemb 10166) h)*PRO.S := by
    nlinarith [hb.1]
  nlinarith [PRO.S_pos]

#print axioms reference_checked
#print axioms center_row_sound
#print axioms all_center_rows_of_blocks
#print axioms witness_checked
#print axioms witness_gap_of_hidden
end PythiaCert.Output
