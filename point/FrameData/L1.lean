import PointData.L1.P0
import PointData.L1.P1
import PointData.L1.P2
import PointData.L1.P3
import PointData.L1.P4
import PointData.L1.P5
import PointData.L1.P6
import PointData.L1.P7
import PointData.L1.P8
import PointData.L1.P9
import PointData.L1.P10
import PointData.L1.P11
import PointData.L1.P12
import PointData.L1.P13
import PointData.L1.P14
import PointData.L1.P15
import PointData.L1.P16
import PointData.L1.P17
import PointData.L1.P18
import PointData.L1.P19
import PointData.L1.P20
import PointData.L1.P21
import PointData.L1.P22
import PointData.L1.P23
import PointData.L1.P24
import PointData.L1.P25
import PointData.L1.P26
import PointData.L1.P27
import PointData.L1.P28
import PointData.L1.P29
import PointData.L1.P30
import PointData.L1.P31
import PointData.L1.P32
import FrameSound
namespace PythiaCert.Frame.L1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cx : List (List PRO.Iv) := [Point.L1P0.x, Point.L1P1.x, Point.L1P2.x, Point.L1P3.x, Point.L1P4.x, Point.L1P5.x, Point.L1P6.x, Point.L1P7.x, Point.L1P8.x, Point.L1P9.x, Point.L1P10.x, Point.L1P11.x, Point.L1P12.x, Point.L1P13.x, Point.L1P14.x, Point.L1P15.x, Point.L1P16.x, Point.L1P17.x, Point.L1P18.x, Point.L1P19.x, Point.L1P20.x, Point.L1P21.x, Point.L1P22.x, Point.L1P23.x, Point.L1P24.x, Point.L1P25.x, Point.L1P26.x, Point.L1P27.x, Point.L1P28.x, Point.L1P29.x, Point.L1P30.x, Point.L1P31.x]
def cq : List (List PRO.Iv) := [Point.L1P0.q, Point.L1P1.q, Point.L1P2.q, Point.L1P3.q, Point.L1P4.q, Point.L1P5.q, Point.L1P6.q, Point.L1P7.q, Point.L1P8.q, Point.L1P9.q, Point.L1P10.q, Point.L1P11.q, Point.L1P12.q, Point.L1P13.q, Point.L1P14.q, Point.L1P15.q, Point.L1P16.q, Point.L1P17.q, Point.L1P18.q, Point.L1P19.q, Point.L1P20.q, Point.L1P21.q, Point.L1P22.q, Point.L1P23.q, Point.L1P24.q, Point.L1P25.q, Point.L1P26.q, Point.L1P27.q, Point.L1P28.q, Point.L1P29.q, Point.L1P30.q, Point.L1P31.q]
def ca : List (List PRO.Iv) := [Point.L1P0.a, Point.L1P1.a, Point.L1P2.a, Point.L1P3.a, Point.L1P4.a, Point.L1P5.a, Point.L1P6.a, Point.L1P7.a, Point.L1P8.a, Point.L1P9.a, Point.L1P10.a, Point.L1P11.a, Point.L1P12.a, Point.L1P13.a, Point.L1P14.a, Point.L1P15.a, Point.L1P16.a, Point.L1P17.a, Point.L1P18.a, Point.L1P19.a, Point.L1P20.a, Point.L1P21.a, Point.L1P22.a, Point.L1P23.a, Point.L1P24.a, Point.L1P25.a, Point.L1P26.a, Point.L1P27.a, Point.L1P28.a, Point.L1P29.a, Point.L1P30.a, Point.L1P31.a]
def ch : List (List PRO.Iv) := [Point.L1P0.h, Point.L1P1.h, Point.L1P2.h, Point.L1P3.h, Point.L1P4.h, Point.L1P5.h, Point.L1P6.h, Point.L1P7.h, Point.L1P8.h, Point.L1P9.h, Point.L1P10.h, Point.L1P11.h, Point.L1P12.h, Point.L1P13.h, Point.L1P14.h, Point.L1P15.h, Point.L1P16.h, Point.L1P17.h, Point.L1P18.h, Point.L1P19.h, Point.L1P20.h, Point.L1P21.h, Point.L1P22.h, Point.L1P23.h, Point.L1P24.h, Point.L1P25.h, Point.L1P26.h, Point.L1P27.h, Point.L1P28.h, Point.L1P29.h, Point.L1P30.h, Point.L1P31.h]
def co : List (List PRO.Iv) := [Point.L1P0.o, Point.L1P1.o, Point.L1P2.o, Point.L1P3.o, Point.L1P4.o, Point.L1P5.o, Point.L1P6.o, Point.L1P7.o, Point.L1P8.o, Point.L1P9.o, Point.L1P10.o, Point.L1P11.o, Point.L1P12.o, Point.L1P13.o, Point.L1P14.o, Point.L1P15.o, Point.L1P16.o, Point.L1P17.o, Point.L1P18.o, Point.L1P19.o, Point.L1P20.o, Point.L1P21.o, Point.L1P22.o, Point.L1P23.o, Point.L1P24.o, Point.L1P25.o, Point.L1P26.o, Point.L1P27.o, Point.L1P28.o, Point.L1P29.o, Point.L1P30.o, Point.L1P31.o]
theorem cx_rows : ∀ X ∈ cx, X.length = 128 := by decide +kernel
theorem co_valid : ∀ X ∈ co, ∀ B ∈ X, B.ok = true := by decide +kernel
def wx : List (List PRO.Iv) := [Point.L1P0.x, Point.L1P1.x, Point.L1P2.x, Point.L1P3.x, Point.L1P4.x, Point.L1P5.x, Point.L1P6.x, Point.L1P7.x, Point.L1P8.x, Point.L1P9.x, Point.L1P10.x, Point.L1P11.x, Point.L1P12.x, Point.L1P13.x, Point.L1P14.x, Point.L1P15.x, Point.L1P16.x, Point.L1P17.x, Point.L1P18.x, Point.L1P19.x, Point.L1P20.x, Point.L1P21.x, Point.L1P22.x, Point.L1P23.x, Point.L1P24.x, Point.L1P25.x, Point.L1P26.x, Point.L1P27.x, Point.L1P28.x, Point.L1P29.x, Point.L1P30.x, Point.L1P32.x]
def wq : List (List PRO.Iv) := [Point.L1P0.q, Point.L1P1.q, Point.L1P2.q, Point.L1P3.q, Point.L1P4.q, Point.L1P5.q, Point.L1P6.q, Point.L1P7.q, Point.L1P8.q, Point.L1P9.q, Point.L1P10.q, Point.L1P11.q, Point.L1P12.q, Point.L1P13.q, Point.L1P14.q, Point.L1P15.q, Point.L1P16.q, Point.L1P17.q, Point.L1P18.q, Point.L1P19.q, Point.L1P20.q, Point.L1P21.q, Point.L1P22.q, Point.L1P23.q, Point.L1P24.q, Point.L1P25.q, Point.L1P26.q, Point.L1P27.q, Point.L1P28.q, Point.L1P29.q, Point.L1P30.q, Point.L1P32.q]
def wa : List (List PRO.Iv) := [Point.L1P0.a, Point.L1P1.a, Point.L1P2.a, Point.L1P3.a, Point.L1P4.a, Point.L1P5.a, Point.L1P6.a, Point.L1P7.a, Point.L1P8.a, Point.L1P9.a, Point.L1P10.a, Point.L1P11.a, Point.L1P12.a, Point.L1P13.a, Point.L1P14.a, Point.L1P15.a, Point.L1P16.a, Point.L1P17.a, Point.L1P18.a, Point.L1P19.a, Point.L1P20.a, Point.L1P21.a, Point.L1P22.a, Point.L1P23.a, Point.L1P24.a, Point.L1P25.a, Point.L1P26.a, Point.L1P27.a, Point.L1P28.a, Point.L1P29.a, Point.L1P30.a, Point.L1P32.a]
def wh : List (List PRO.Iv) := [Point.L1P0.h, Point.L1P1.h, Point.L1P2.h, Point.L1P3.h, Point.L1P4.h, Point.L1P5.h, Point.L1P6.h, Point.L1P7.h, Point.L1P8.h, Point.L1P9.h, Point.L1P10.h, Point.L1P11.h, Point.L1P12.h, Point.L1P13.h, Point.L1P14.h, Point.L1P15.h, Point.L1P16.h, Point.L1P17.h, Point.L1P18.h, Point.L1P19.h, Point.L1P20.h, Point.L1P21.h, Point.L1P22.h, Point.L1P23.h, Point.L1P24.h, Point.L1P25.h, Point.L1P26.h, Point.L1P27.h, Point.L1P28.h, Point.L1P29.h, Point.L1P30.h, Point.L1P32.h]
def wo : List (List PRO.Iv) := [Point.L1P0.o, Point.L1P1.o, Point.L1P2.o, Point.L1P3.o, Point.L1P4.o, Point.L1P5.o, Point.L1P6.o, Point.L1P7.o, Point.L1P8.o, Point.L1P9.o, Point.L1P10.o, Point.L1P11.o, Point.L1P12.o, Point.L1P13.o, Point.L1P14.o, Point.L1P15.o, Point.L1P16.o, Point.L1P17.o, Point.L1P18.o, Point.L1P19.o, Point.L1P20.o, Point.L1P21.o, Point.L1P22.o, Point.L1P23.o, Point.L1P24.o, Point.L1P25.o, Point.L1P26.o, Point.L1P27.o, Point.L1P28.o, Point.L1P29.o, Point.L1P30.o, Point.L1P32.o]
theorem wx_rows : ∀ X ∈ wx, X.length = 128 := by decide +kernel
theorem wo_valid : ∀ X ∈ wo, ∀ B ∈ X, B.ok = true := by decide +kernel
theorem decode : CompletionBridge.decodeLayer (PRO.LL 1) = CON.layer1 := by
  simp only [CON.layer1, mat_eq, row_eq_vec]
  rfl
theorem qkv_rows : (PRO.LL 1).qkvW.length = 384 := by decide +kernel
end PythiaCert.Frame.L1
