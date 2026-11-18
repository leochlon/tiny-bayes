import FixedEval
namespace BoundsInterval

lemma sqLo_step (k : ℕ) (a b c : ℤ) (h : fdiv (a*a) S = b)
    (hr : sqLo k b = c) : sqLo (k+1) a = c := by
  simpa only [sqLo, h] using hr

lemma sqHi_step (k : ℕ) (a b c : ℤ) (h : cdiv (a*a) S = b)
    (hr : sqHi k b = c) : sqHi (k+1) a = c := by
  simpa only [sqHi, h] using hr

lemma expI_from_steps (n a b l u : ℤ)
    (ha : max 0 (S + fdiv n TWO_M) = a)
    (hb : cdiv (S*SM) (SM-n) = b)
    (hl : sqLo M a = l) (hu : sqHi M b = u) (hn : n < SM) :
    expI (cst n) = ⟨l,u,true⟩ := by
  simp only [expI, cst, expLo, expHi, ha, hb, hl, hu]
  simp [hn]

#print axioms expI_from_steps
end BoundsInterval
