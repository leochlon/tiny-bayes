import PINN.Interval

/-! Pieces 252..257 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C042

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1213316, 1221145, -3086434062938535, -1444322843640641),
  (1221145, 1223338, -2311315047620801, -2175666404278049),
  (1223338, 1231210, -3044889877403557, -1395363148928955),
  (1231210, 1239082, -3001589401815455, -1360363748138088),
  (1239082, 1247018, -2968200348170612, -1309214513102378),
  (1247018, 1254918, -2911315374820340, -1275990233220035)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1213316, 1221145, -3086434062938535, -1444322843640641) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1221145, 1223338, -2311315047620801, -2175666404278049) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1223338, 1231210, -3044889877403557, -1395363148928955) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1231210, 1239082, -3001589401815455, -1360363748138088) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1239082, 1247018, -2968200348170612, -1309214513102378) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1247018, 1254918, -2911315374820340, -1275990233220035) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C042
