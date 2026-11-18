import Input
import NextCommon
import LayerBridge
import PRO.Compose

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem layer0_decode : CompletionBridge.decodeLayer (PRO.LL 0) = CON.layer0 := by
  simp only [CON.layer0, mat_eq, row_eq_vec]
  rfl

theorem layer0_qkv_rows : (PRO.LL 0).qkvW.length = 384 := by decide +kernel

def embeddingBits (t : Nat) : Nat := (CON.W.eChunks.getD (t/256) []).getD (t%256) 0
def embeddingBox (t : Nat) : List PRO.Iv := PRO.vecI (embeddingBits t) 128

theorem embedding_sound (t : Nat) :
    List.Forall₂ (PRO.memAt PRO.S) (CON.pythia14m.emb t) (embeddingBox t) :=
  row_sound _ _

theorem embedding_length (t : Nat) : (CON.pythia14m.emb t).length = 128 := row_length _ _

theorem qCheck_sound (L : PRO.Layer) {x : List ℝ} {X Q : List PRO.Iv}
    (hxlen : x.length = 128) (hx : List.Forall₂ (PRO.memAt PRO.S) x X)
    (hc : PRO.qCheck L X Q = true) :
    List.Forall₂ (PRO.memAt PRO.S)
      (CON.qkv (CompletionBridge.decodeLayer L)
        (CON.layerNorm (CompletionBridge.decodeLayer L).ln1g
          (CompletionBridge.decodeLayer L).ln1b x)) Q := by
  rw [CompletionBridge.qkv_eq, CompletionBridge.layerNorm_eq _ _ _ hxlen]
  simp only [PRO.qCheck, PRO.stList_eq] at hc
  exact f2_sub (PRO.f2_lin _ _ _ _ (PRO.f2_layerNorm _ _ hx)) Q hc

theorem layer0_qCheck_sound (t : Nat) {X Q : List PRO.Iv}
    (he : PRO.allSub (embeddingBox t) X = true)
    (hq : PRO.qCheck (PRO.LL 0) X Q = true) :
    List.Forall₂ (PRO.memAt PRO.S)
      (CON.qkv CON.layer0 (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b (CON.pythia14m.emb t))) Q := by
  rw [← layer0_decode]
  exact qCheck_sound _ (embedding_length t) (f2_sub (embedding_sound t) X he) hq

#print axioms layer0_qCheck_sound
end PythiaCert
