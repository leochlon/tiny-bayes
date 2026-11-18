import PointStates
import FrameNumeric.L2
import FrameStep.L1
namespace PythiaCert.Frame.L2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cinput_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) Frame.L1.cstate cx := by
  exact Frame.L1.cstate_mem
theorem cstate_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) cstate co := by
  unfold cstate
  rw [← decode]
  exact checked_con_layer (PRO.LL 2) (Bq := cq) (Ba := ca) (Bh := ch) (Bo := co) qkv_rows cinput_mem cx_rows rfl rfl cq_checks ca_checks ch_checks co_checks
theorem actual_c_state_enclosed : List.Forall₂ (List.Forall₂ Encloses) cstate co :=
  discharge_matrix cstate_mem co_valid
#print axioms actual_c_state_enclosed
theorem winput_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) Frame.L1.wstate wx := by
  exact Frame.L1.wstate_mem
theorem wstate_mem : List.Forall₂ (List.Forall₂ (PRO.memAt PRO.S)) wstate wo := by
  unfold wstate
  rw [← decode]
  exact checked_con_layer (PRO.LL 2) (Bq := wq) (Ba := wa) (Bh := wh) (Bo := wo) qkv_rows winput_mem wx_rows rfl rfl wq_checks wa_checks wh_checks wo_checks
theorem actual_w_state_enclosed : List.Forall₂ (List.Forall₂ Encloses) wstate wo :=
  discharge_matrix wstate_mem wo_valid
#print axioms actual_w_state_enclosed
end PythiaCert.Frame.L2
