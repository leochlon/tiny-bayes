import PointStates
import FrameNumeric.L5
import FrameStep.L4
namespace PythiaCert.Frame.L5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cinput_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) Frame.L4.cstate cx := by
  exact Frame.L4.cstate_mem
theorem clast_mem : List.Forall₂ (PRO.memAt PRO.S) (cstate.getD 31 []) Point.L5P31.o := by
  unfold cstate
  rw [← decode]
  have hlen : Frame.L4.cstate.length = 32 := cinput_mem.length_eq
  rw [con_layer_get (PRO.LL 5) _ 31 qkv_rows (rows_length_of_boxes cinput_mem cx_rows) (by omega)]
  exact checked_block_row (PRO.LL 5) _ 31 (PRO.f2_getD List.Forall₂.nil cinput_mem 31)
    (q_matrix_sound (PRO.LL 5) (Bq := cq) cinput_mem rfl cq_checks)
    Point.L5P31.a_check Point.L5P31.h_check Point.L5P31.o_check
theorem actual_c_last_enclosed : List.Forall₂ Encloses (cstate.getD 31 []) Point.L5P31.o :=
  discharge_valid clast_mem (by decide +kernel)
#print axioms actual_c_last_enclosed
theorem winput_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) Frame.L4.wstate wx := by
  exact Frame.L4.wstate_mem
theorem wlast_mem : List.Forall₂ (PRO.memAt PRO.S) (wstate.getD 31 []) Point.L5P32.o := by
  unfold wstate
  rw [← decode]
  have hlen : Frame.L4.wstate.length = 32 := winput_mem.length_eq
  rw [con_layer_get (PRO.LL 5) _ 31 qkv_rows (rows_length_of_boxes winput_mem wx_rows) (by omega)]
  exact checked_block_row (PRO.LL 5) _ 31 (PRO.f2_getD List.Forall₂.nil winput_mem 31)
    (q_matrix_sound (PRO.LL 5) (Bq := wq) winput_mem rfl wq_checks)
    Point.L5P32.a_check Point.L5P32.h_check Point.L5P32.o_check
theorem actual_w_last_enclosed : List.Forall₂ Encloses (wstate.getD 31 []) Point.L5P32.o :=
  discharge_valid wlast_mem (by decide +kernel)
#print axioms actual_w_last_enclosed
end PythiaCert.Frame.L5
