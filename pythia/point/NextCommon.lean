import NextData

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mat_eq (m : Nat) (rs : List Nat) : CON.mat m rs = PRO.mat rs m := by
  unfold CON.mat PRO.mat
  apply List.map_congr_left
  intro r _
  exact row_eq_vec m r

theorem lin_sound (rs : List Nat) (n bias m : Nat) {x : List ℝ} {X : List PRO.Iv}
    (hx : List.Forall₂ (PRO.memAt PRO.S) x X) :
    List.Forall₂ (PRO.memAt PRO.S)
      (CON.vadd (CON.mv (CON.mat n rs) x) (CON.row m bias)) (PRO.linI rs n bias m X) := by
  rw [mat_eq, row_eq_vec]
  exact PRO.f2_lin rs n bias m hx

theorem ln31Box_sound : List.Forall₂ (PRO.memAt PRO.S) ln31 ln31Box :=
  f2_sub ln31_sound ln31Box ln31_check

end PythiaCert
