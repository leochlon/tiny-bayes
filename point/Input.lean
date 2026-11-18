import Bridge

namespace PythiaCert

def tokens : List Nat := [0, 34, 10166, 11454, 2990, 8115, 247, 3425,
  273, 21761, 281, 7363, 323, 253, 1735, 10669, 15, 844, 476, 7472,
  1798, 14800, 13, 7277, 13650, 13, 285, 1071, 10151, 46234, 15, 329]

def inputBits : Nat := CON.W.e1.getD 73 0
noncomputable def input : List (List ℝ) := tokens.map CON.pythia14m.emb
noncomputable def input31 : List ℝ := input.getD 31 []

theorem tokens_length : tokens.length = 32 := by decide +kernel
theorem tokens_last : tokens.getD 31 0 = 329 := by decide +kernel
theorem input31_eq : input31 = CON.row 128 inputBits := rfl
theorem input31_length : input31.length = 128 := by
  rw [input31_eq]
  exact row_length _ _

def input31I : List PRO.Iv := PRO.vecI inputBits 128
theorem input31_sound : List.Forall₂ (PRO.memAt PRO.S) input31 input31I := by
  rw [input31_eq]
  exact row_sound _ _

def ln31I : List PRO.Iv :=
  PRO.layerNormI CON.W.L0.ln1g CON.W.L0.ln1b input31I

noncomputable def ln31 : List ℝ :=
  CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b input31

theorem ln31_sound : List.Forall₂ (PRO.memAt PRO.S) ln31 ln31I :=
  layerNorm_sound _ _ input31_length input31_sound

end PythiaCert
