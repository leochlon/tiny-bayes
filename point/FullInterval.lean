import NextCommon

namespace PythiaCert

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open PRO

noncomputable def decodeLayer (L : PRO.Layer) : CON.Layer where
  ln1g := CON.row 128 L.ln1g
  ln1b := CON.row 128 L.ln1b
  ln2g := CON.row 128 L.ln2g
  ln2b := CON.row 128 L.ln2b
  qkvW := CON.mat 128 L.qkvW
  qkvB := CON.row 384 L.qkvB
  oW := CON.mat 128 L.dW
  oB := CON.row 128 L.dB
  fW := CON.mat 128 L.fcW
  fB := CON.row 512 L.fcB
  pW := CON.mat 512 L.pjW
  pB := CON.row 128 L.pjB

def rotaryI (m : Nat) (U : List PRO.Iv) : List PRO.Iv :=
  (List.range U.length).map fun i =>
    if i < 4 then PRO.add (PRO.mul (U.getD i PRO.zero) (PRO.cosT m i))
      (PRO.neg (PRO.mul (U.getD (i+4) PRO.zero) (PRO.sinT m i)))
    else if i < 8 then PRO.add (PRO.mul (U.getD i PRO.zero) (PRO.cosT m (i-4)))
      (PRO.mul (U.getD (i-4) PRO.zero) (PRO.sinT m (i-4)))
    else U.getD i PRO.zero

theorem rotary_sound (m : Nat) {u : List ℝ} {U : List PRO.Iv}
    (hu : List.Forall₂ (PRO.memAt PRO.S) u U) :
    List.Forall₂ (PRO.memAt PRO.S) (CON.rotary m u) (rotaryI m U) := by
  unfold CON.rotary rotaryI
  rw [hu.length_eq]
  apply PRO.f2_map_same
  intro i
  have g := fun j => PRO.f2_getD (PRO.memAt_zero PRO.S) hu j
  by_cases h4 : i < 4
  · simp only [if_pos h4]
    simpa only [sub_eq_add_neg] using
      PRO.memAt_add (PRO.memAt_mul (g i) (PRO.memAt_cosT m i))
        (PRO.memAt_neg (PRO.memAt_mul (g (i+4)) (PRO.memAt_sinT m i)))
  · by_cases h8 : i < 8
    · simp only [if_neg h4, if_pos h8]
      exact PRO.memAt_add (PRO.memAt_mul (g i) (PRO.memAt_cosT m (i-4)))
        (PRO.memAt_mul (g (i-4)) (PRO.memAt_sinT m (i-4)))
    · simp only [if_neg h4, if_neg h8]
      exact g i

def mixI (Ws : List PRO.Iv) (Vs : List (List PRO.Iv)) : List PRO.Iv :=
  (List.range 32).map fun d => PRO.downBy PRO.S
    (PRO.sumI (List.zipWith (fun w v => PRO.mulRaw w (v.getD d PRO.zero)) Ws Vs))

theorem mix_sound {w : List ℝ} {W : List PRO.Iv} {v : List (List ℝ)} {V : List (List PRO.Iv)}
    (hw : List.Forall₂ (PRO.memAt PRO.S) w W)
    (hv : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) v V) :
    List.Forall₂ (PRO.memAt PRO.S) (CON.mix w v) (mixI W V) := by
  unfold CON.mix mixI
  exact PRO.f2_map_same (fun d => PRO.memAt_downBy PRO.S_pos_int (PRO.memAt_sum
    (PRO.f2_zipWith (R₁ := PRO.memAt PRO.S) (R₂ := List.Forall₂ (PRO.memAt PRO.S))
      (R := PRO.memAt ((PRO.S : ℝ) * PRO.S))
      (f := fun w v => w * v.getD d 0)
      (g := fun w v => PRO.mulRaw w (v.getD d PRO.zero))
      (fun _ _ _ _ h1 h2 => PRO.memAt_mulRaw h1 (PRO.f2_getD (PRO.memAt_zero PRO.S) h2 d))
      hw hv))) (List.range 32)

theorem softmax_sound {s : List ℝ} {S : List PRO.Iv}
    (hs : List.Forall₂ (PRO.memAt PRO.S) s S) :
    List.Forall₂ (PRO.memAt PRO.S) (CON.softmax s) (PRO.softmaxI S) := by
  simpa only [CON.softmax, PRO.softmax, List.map_map] using PRO.f2_softmax hs

noncomputable def headValues (Q : List (List ℝ)) (j h : Nat) : List ℝ :=
  let vis := Q.take (j+1)
  let q := CON.rotary j (((Q.getD j []).drop (96*h)).take 32)
  let ks := List.zipWith (fun i u => CON.rotary i ((u.drop (96*h+32)).take 32)) (List.range (j+1)) vis
  let vs := vis.map fun u => (u.drop (96*h+64)).take 32
  CON.mix (CON.softmax (ks.map fun k => CON.dot q k / Real.sqrt 32)) vs

def headValuesI (Q : List (List PRO.Iv)) (j h : Nat) : List PRO.Iv :=
  let vis := Q.take (j+1)
  let q := rotaryI j (((Q.getD j []).drop (96*h)).take 32)
  let ks := List.zipWith (fun i u => rotaryI i ((u.drop (96*h+32)).take 32)) (List.range (j+1)) vis
  let vs := vis.map fun u => (u.drop (96*h+64)).take 32
  let rs := PRO.recip (PRO.sqrtI ⟨32 * PRO.S, 32 * PRO.S, true⟩)
  mixI (PRO.softmaxI (ks.map fun k => PRO.mul (PRO.dotI q k) rs)) vs

theorem headValues_sound (j h : Nat) {q : List (List ℝ)} {Q : List (List PRO.Iv)}
    (hq : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) q Q) :
    List.Forall₂ (PRO.memAt PRO.S) (headValues q j h) (headValuesI Q j h) := by
  unfold headValues headValuesI
  have hqt := List.forall₂_take (j+1) hq
  have hqj := PRO.f2_getD (R := List.Forall₂ (PRO.memAt PRO.S)) List.Forall₂.nil hq j
  have hquery := rotary_sound j (PRO.f2_slice (96*h) 32 hqj)
  have hkeys := PRO.f2_zipWith_left
    (R := List.Forall₂ (PRO.memAt PRO.S)) (R' := List.Forall₂ (PRO.memAt PRO.S))
    (f := fun i u => CON.rotary i ((u.drop (96*h+32)).take 32))
    (g := fun i u => rotaryI i ((u.drop (96*h+32)).take 32))
    (fun i _ _ hu => rotary_sound i (PRO.f2_slice (96*h+32) 32 hu)) (List.range (j+1)) hqt
  have hvalues := PRO.f2_map (fun _ _ hu => PRO.f2_slice (96*h+64) 32 hu) hqt
  have hrs := PRO.memAt_recip (PRO.memAt_sqrt PRO.memAt_32)
  exact mix_sound (softmax_sound
    (PRO.f2_map (fun _ _ hk => PRO.memAt_div (PRO.memAt_dotI hquery hk) hrs) hkeys)) hvalues

theorem getD_map_lt {α β : Type*} (f : α → β) (da : α) (db : β) :
    ∀ (xs : List α) (j : Nat), j < xs.length → (xs.map f).getD j db = f (xs.getD j da)
  | [], _, hj => by simp at hj
  | _::_, 0, _ => rfl
  | _::xs, j+1, hj => by
    simpa using getD_map_lt f da db xs j (by simpa using hj)

theorem headOut_eq (L : CON.Layer) (U : List (List ℝ)) (j h : Nat) (hj : j < U.length) :
    CON.headOut L U j h = headValues (U.map (CON.qkv L)) j h := by
  unfold CON.headOut headValues
  rw [getD_map_lt (CON.qkv L) [] [] U j hj, CON.take_map_eq]
  simp only [List.zipWith_map_right, List.map_map, Function.comp_def]

def attentionI (L : PRO.Layer) (Q : List (List PRO.Iv)) (j : Nat) : List PRO.Iv :=
  PRO.linI L.dW 128 L.dB 128 ((List.range 4).flatMap fun h => headValuesI Q j h)

theorem f2_flatMap_same {α β γ : Type*} {R : β → γ → Prop} {f : α → List β} {g : α → List γ}
    (h : ∀ a, List.Forall₂ R (f a) (g a)) : ∀ xs : List α,
      List.Forall₂ R (xs.flatMap f) (xs.flatMap g)
  | [] => .nil
  | a::xs => by simpa using PRO.f2_append (h a) (f2_flatMap_same h xs)

theorem attention_sound (L : PRO.Layer) {u : List (List ℝ)} {Q : List (List PRO.Iv)}
    (hq : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) (u.map (CON.qkv (decodeLayer L))) Q)
    (j : Nat) (hj : j < u.length) :
    List.Forall₂ (PRO.memAt PRO.S) (CON.attnOut (decodeLayer L) u j) (attentionI L Q j) := by
  unfold CON.attnOut attentionI
  apply lin_sound
  apply f2_flatMap_same
  intro h
  rw [headOut_eq _ _ _ _ hj]
  exact headValues_sound _ _ hq

def hiddenI (L : PRO.Layer) (X : List PRO.Iv) : List PRO.Iv :=
  (PRO.linI L.fcW 128 L.fcB 512 (PRO.layerNormI L.ln2g L.ln2b X)).map PRO.geluI

theorem hidden_sound (L : PRO.Layer) {x : List ℝ} {X : List PRO.Iv}
    (hlen : x.length = 128) (hx : List.Forall₂ (PRO.memAt PRO.S) x X) :
    List.Forall₂ (PRO.memAt PRO.S)
      ((CON.vadd (CON.mv (decodeLayer L).fW
        (CON.layerNorm (decodeLayer L).ln2g (decodeLayer L).ln2b x)) (decodeLayer L).fB).map CON.gelu)
      (hiddenI L X) :=
  PRO.f2_map (fun _ _ h => PRO.memAt_gelu h)
    (lin_sound _ _ _ _ (layerNorm_sound _ _ hlen hx))

#print axioms attention_sound
#print axioms hidden_sound

end PythiaCert
