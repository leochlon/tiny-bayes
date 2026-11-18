import PointLink
import Shard

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows_length_of_boxes {xs : List (List ℝ)} {Xs : List (List PRO.Iv)}
    (hx : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) xs Xs)
    (hX : ∀ X ∈ Xs, X.length = 128) : ∀ x ∈ xs, x.length = 128 := by
  induction hx with
  | nil => simp
  | @cons x X xs Xs h hxs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.length_eq.trans (hX X (by simp))
    · exact ih (fun Y hY => hX Y (by simp [hY])) y hy

theorem discharge_matrix {xs : List (List ℝ)} {Xs : List (List PRO.Iv)}
    (hx : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) xs Xs)
    (hX : ∀ X ∈ Xs, ∀ B ∈ X, B.ok = true) :
    List.Forall₂ (List.Forall₂ Encloses) xs Xs := by
  induction hx with
  | nil => exact .nil
  | @cons x X xs Xs h hxs ih =>
    exact .cons (discharge_valid h (hX X (by simp)))
      (ih (fun Y hY => hX Y (by simp [hY])))

theorem checked_con_layer (L : PRO.Layer) {xs : List (List ℝ)}
    {Bx Bq Ba Bh Bo : List (List PRO.Iv)}
    (hqr : L.qkvW.length = 384)
    (hx : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) xs Bx)
    (hX : ∀ X ∈ Bx, X.length = 128)
    (hlq : Bq.length = Bx.length) (hlo : Bo.length = Bx.length)
    (hq : ∀ i, i < Bx.length → PRO.qCheck L (Bx.getD i []) (Bq.getD i []) = true)
    (ha : ∀ i, i < Bx.length → PRO.aCheck L i (Bq.take (i+1)) (Ba.getD i []) = true)
    (hh : ∀ i, i < Bx.length → PRO.hCheck L (Bx.getD i []) (Bh.getD i []) = true)
    (ho : ∀ i, i < Bx.length → PRO.oCheck L (Bx.getD i []) (Ba.getD i [])
      (Bh.getD i []) (Bo.getD i []) = true) :
    List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S))
      (CON.layer (CompletionBridge.decodeLayer L) xs) Bo := by
  rw [CompletionBridge.layer_eq_block L hqr xs (rows_length_of_boxes hx hX)]
  exact PRO.layer_ok L hx hlq hlo hq ha hh ho

theorem q_matrix_sound (L : PRO.Layer) {xs : List (List ℝ)} {Bx Bq : List (List PRO.Iv)}
    (hx : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) xs Bx)
    (hlq : Bq.length = Bx.length)
    (hq : ∀ i, i < Bx.length → PRO.qCheck L (Bx.getD i []) (Bq.getD i []) = true) :
    List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) (xs.map (PRO.qkvR L)) Bq := by
  have hlen := hx.length_eq
  refine PRO.f2_of_getD (PRO.qkvR L []) [] (by simp [hlen, hlq]) fun i hi => ?_
  rw [List.getD_map (f := PRO.qkvR L)]
  have hi' : i < Bx.length := by simpa [hlen] using hi
  have hc := hq i hi'
  simp only [PRO.qCheck, PRO.stList_eq] at hc
  unfold PRO.qkvR
  exact PRO.f2_sub (PRO.f2_lin L.qkvW 128 L.qkvB 384
    (PRO.f2_layerNorm L.ln1g L.ln1b (PRO.f2_getD List.Forall₂.nil hx i))) _ hc

theorem checked_block_row (L : PRO.Layer) (xs : List (List ℝ)) (i : Nat)
    {X : List PRO.Iv} {Q : List (List PRO.Iv)} {A H O : List PRO.Iv}
    (hx : List.Forall₂ (PRO.memAt PRO.S) (xs.getD i []) X)
    (hq : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) (xs.map (PRO.qkvR L)) Q)
    (ha : PRO.aCheck L i (Q.take (i+1)) A = true)
    (hh : PRO.hCheck L X H = true)
    (ho : PRO.oCheck L X A H O = true) :
    List.Forall₂ (PRO.memAt PRO.S) (PRO.blockAt L xs i) O := by
  have hatt := PRO.f2_sub (PRO.f2_attn L i (List.forall₂_take (i+1) hq)) _ ha
  simp only [PRO.hCheck, PRO.stList_eq] at hh
  have hhid := PRO.f2_sub (PRO.f2_map (R := PRO.memAt PRO.S) (R' := PRO.memAt PRO.S)
    (f := PRO.gelu) (g := PRO.geluI) (fun _ _ h => PRO.memAt_gelu h)
    (PRO.f2_lin L.fcW 128 L.fcB 512 (PRO.f2_layerNorm L.ln2g L.ln2b hx))) _ hh
  have hm := PRO.f2_lin L.pjW 512 L.pjB 128 hhid
  exact PRO.f2_sub (PRO.f2_vadd (PRO.f2_vadd hx hatt) hm) _ ho

theorem con_layer_get (L : PRO.Layer) (xs : List (List ℝ)) (i : Nat)
    (hqr : L.qkvW.length = 384) (hxs : ∀ x ∈ xs, x.length = 128) (hi : i < xs.length) :
    (CON.layer (CompletionBridge.decodeLayer L) xs).getD i [] = PRO.blockAt L xs i := by
  rw [CompletionBridge.layer_eq_block L hqr xs hxs, PRO.block_eq,
    CompletionBridge.map_getD_in _ _ 0 [] i (by simpa using hi)]
  congr 1
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

#print axioms checked_con_layer
#print axioms checked_block_row
#print axioms con_layer_get
end PythiaCert
