import PRO.Model
import CON.Model

set_option maxRecDepth 10000

namespace CompletionBridge
noncomputable section

def decodeLayer (L : PRO.Layer) : CON.Layer where
  ln1g := PRO.vec L.ln1g 128
  ln1b := PRO.vec L.ln1b 128
  ln2g := PRO.vec L.ln2g 128
  ln2b := PRO.vec L.ln2b 128
  qkvW := PRO.mat L.qkvW 128
  qkvB := PRO.vec L.qkvB 384
  oW := PRO.mat L.dW 128
  oB := PRO.vec L.dB 128
  fW := PRO.mat L.fcW 128
  fB := PRO.vec L.fcB 512
  pW := PRO.mat L.pjW 512
  pB := PRO.vec L.pjB 128

theorem layerNorm_eq (g b x : List ℝ) (hx : x.length = 128) :
    CON.layerNorm g b x = PRO.layerNorm g b x := by
  simp only [CON.layerNorm, PRO.layerNorm, PRO.lnMean, PRO.lnInvStd, hx,
    Nat.cast_ofNat, div_eq_mul_inv]
  rfl

theorem qkv_eq (L : PRO.Layer) (u : List ℝ) :
    CON.qkv (decodeLayer L) u = PRO.lin (PRO.mat L.qkvW 128) (PRO.vec L.qkvB 384) u := rfl

theorem qkv_length (L : PRO.Layer) (hq : L.qkvW.length = 384) (u : List ℝ) :
    (CON.qkv (decodeLayer L) u).length = 384 := by
  simp [CON.qkv, decodeLayer, CON.vadd, CON.mv, PRO.mat, PRO.vec, hq]

theorem rotary_eq (j : ℕ) (u : List ℝ) (hu : u.length = 32) :
    CON.rotary j u = PRO.rot j u := by
  simp only [CON.rotary, PRO.rot, hu]

theorem softmax_eq (s : List ℝ) : CON.softmax s = PRO.softmax s := by
  simp [CON.softmax, PRO.softmax, List.map_map]

theorem map_getD_in {α β : Type*} (xs : List α) (f : α → β)
    (da : α) (db : β) (i : ℕ) (hi : i < xs.length) :
    (xs.map f).getD i db = f (xs.getD i da) := by
  rw [List.getD_eq_getElem (xs.map f) db (by simpa using hi), List.getD_eq_getElem xs da hi]
  simp

theorem zip_range_take {α β : Type*} (xs : List α) (da : α) (f : ℕ → α → β)
    (n : ℕ) (hn : n ≤ xs.length) :
    List.zipWith f (List.range n) (xs.take n) =
      (List.range n).map (fun i => f i (xs.getD i da)) := by
  apply List.ext_getElem
  · simp [List.length_zipWith, List.length_take, min_eq_left hn]
  · intro i hi hj
    have hin : i < n := by simpa using hj
    have hix : i < xs.length := lt_of_lt_of_le hin hn
    simp only [List.getElem_zipWith, List.getElem_range, List.getElem_take, List.getElem_map,
      List.getD_eq_getElem xs da hix]

theorem qrows_getD (L : PRO.Layer) (U : List (List ℝ)) (n i : ℕ)
    (hin : i < n) (hiU : i < U.length) :
    ((U.map (CON.qkv (decodeLayer L))).take n).getD i [] =
      CON.qkv (decodeLayer L) (U.getD i []) := by
  rw [CON.getD_take_prefix _ _ _ _ hin]
  exact map_getD_in U _ [] [] i hiU

theorem qkv_slice_length (L : PRO.Layer) (hq : L.qkvW.length = 384)
    (u : List ℝ) (h : ℕ) (hh : h < 4) (k : ℕ) (hk : k ≤ 64) :
    (((CON.qkv (decodeLayer L) u).drop (96*h+k)).take 32).length = 32 := by
  simp only [List.length_take, List.length_drop, qkv_length L hq]
  omega

theorem headOut_eq (L : PRO.Layer) (hq : L.qkvW.length = 384)
    (U : List (List ℝ)) (j h : ℕ) (hj : j < U.length) (hh : h < 4) :
    CON.headOut (decodeLayer L) U j h =
      PRO.headOut j ((U.map (CON.qkv (decodeLayer L))).take (j+1)) h := by
  let Q := (U.map (CON.qkv (decodeLayer L))).take (j+1)
  have hquery : CON.rotary j (((CON.qkv (decodeLayer L) (U.getD j [])).drop (96*h)).take 32) =
      PRO.rot j (PRO.slice (Q.getD j []) (96*h) 32) := by
    dsimp [Q, PRO.slice]
    rw [qrows_getD L U (j+1) j (by omega) hj]
    exact rotary_eq j _ (by simpa using qkv_slice_length L hq (U.getD j []) h hh 0 (by omega))
  have hkeys : List.zipWith (fun i u => CON.rotary i
      (((CON.qkv (decodeLayer L) u).drop (96*h+32)).take 32))
      (List.range (j+1)) (U.take (j+1)) =
      (List.range (j+1)).map (fun i => PRO.rot i (PRO.slice (Q.getD i []) (96*h+32) 32)) := by
    rw [zip_range_take U [] _ (j+1) (by omega)]
    apply List.map_congr_left
    intro i hi
    have hi' : i < j+1 := List.mem_range.mp hi
    dsimp [Q, PRO.slice]
    rw [qrows_getD L U (j+1) i hi' (by omega)]
    exact rotary_eq i _ (qkv_slice_length L hq (U.getD i []) h hh 32 (by omega))
  have hvals : (U.take (j+1)).map (fun u =>
      ((CON.qkv (decodeLayer L) u).drop (96*h+64)).take 32) =
      Q.map (fun u => PRO.slice u (96*h+64) 32) := by
    simp [Q, PRO.slice, List.map_map, Function.comp_def]
  unfold CON.headOut PRO.headOut
  change CON.mix (CON.softmax ((List.zipWith _ (List.range (j+1)) (U.take (j+1))).map
    (fun k => CON.dot _ k / Real.sqrt 32))) _ = _
  rw [hkeys, hquery, hvals, softmax_eq]
  simp only [CON.mix, List.map_map, Function.comp_apply, CON.dot, PRO.dot, div_eq_mul_inv]
  rfl

theorem attnOut_eq (L : PRO.Layer) (hq : L.qkvW.length = 384)
    (U : List (List ℝ)) (j : ℕ) (hj : j < U.length) :
    CON.attnOut (decodeLayer L) U j =
      PRO.attn L j ((U.map (CON.qkv (decodeLayer L))).take (j+1)) := by
  unfold CON.attnOut PRO.attn
  have hrange : List.range 4 = [0,1,2,3] := by decide
  rw [hrange]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [headOut_eq L hq U j 0 hj (by decide), headOut_eq L hq U j 1 hj (by decide),
    headOut_eq L hq U j 2 hj (by decide), headOut_eq L hq U j 3 hj (by decide)]
  simp only [List.append_assoc]
  rfl

theorem mlpOut_eq (L : PRO.Layer) (u : List ℝ) :
    CON.mlpOut (decodeLayer L) u = PRO.mlp L u := rfl

/-- Complete graph equivalence for arbitrary finite prompt lengths. The hypotheses
    state dimensions, not unverified numerical enclosures. -/
theorem layer_eq_block (L : PRO.Layer) (hq : L.qkvW.length = 384)
    (xs : List (List ℝ)) (hxs : ∀ x ∈ xs, x.length = 128) :
    CON.layer (decodeLayer L) xs = PRO.block L xs := by
  unfold CON.layer PRO.block
  apply List.map_congr_left
  intro j hj
  have hj' : j < xs.length := List.mem_range.mp hj
  have hrow : (xs.getD j []).length = 128 := by
    rw [List.getD_eq_getElem xs [] hj']
    exact hxs _ (List.getElem_mem hj')
  have hmap : xs.map (CON.layerNorm (decodeLayer L).ln1g (decodeLayer L).ln1b) =
      xs.map (PRO.layerNorm (PRO.vec L.ln1g 128) (PRO.vec L.ln1b 128)) := by
    apply List.map_congr_left
    intro x hx
    exact layerNorm_eq _ _ _ (hxs x hx)
  rw [attnOut_eq L hq _ j (by simpa using hj'), hmap, mlpOut_eq,
    layerNorm_eq _ _ _ hrow]
  simp only [List.map_map, Function.comp_apply, qkv_eq]
  rfl

#print axioms layer_eq_block
#check layer_eq_block
end
end CompletionBridge
