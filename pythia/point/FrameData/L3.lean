import PointData.L3.P0
import PointData.L3.P1
import PointData.L3.P2
import PointData.L3.P3
import PointData.L3.P4
import PointData.L3.P5
import PointData.L3.P6
import PointData.L3.P7
import PointData.L3.P8
import PointData.L3.P9
import PointData.L3.P10
import PointData.L3.P11
import PointData.L3.P12
import PointData.L3.P13
import PointData.L3.P14
import PointData.L3.P15
import PointData.L3.P16
import PointData.L3.P17
import PointData.L3.P18
import PointData.L3.P19
import PointData.L3.P20
import PointData.L3.P21
import PointData.L3.P22
import PointData.L3.P23
import PointData.L3.P24
import PointData.L3.P25
import PointData.L3.P26
import PointData.L3.P27
import PointData.L3.P28
import PointData.L3.P29
import PointData.L3.P30
import PointData.L3.P31
import PointData.L3.P32
import FrameSound
namespace PythiaCert.Frame.L3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cx : List (List PRO.Iv) := [Point.L3P0.x, Point.L3P1.x, Point.L3P2.x, Point.L3P3.x, Point.L3P4.x, Point.L3P5.x, Point.L3P6.x, Point.L3P7.x, Point.L3P8.x, Point.L3P9.x, Point.L3P10.x, Point.L3P11.x, Point.L3P12.x, Point.L3P13.x, Point.L3P14.x, Point.L3P15.x, Point.L3P16.x, Point.L3P17.x, Point.L3P18.x, Point.L3P19.x, Point.L3P20.x, Point.L3P21.x, Point.L3P22.x, Point.L3P23.x, Point.L3P24.x, Point.L3P25.x, Point.L3P26.x, Point.L3P27.x, Point.L3P28.x, Point.L3P29.x, Point.L3P30.x, Point.L3P31.x]
def cq : List (List PRO.Iv) := [Point.L3P0.q, Point.L3P1.q, Point.L3P2.q, Point.L3P3.q, Point.L3P4.q, Point.L3P5.q, Point.L3P6.q, Point.L3P7.q, Point.L3P8.q, Point.L3P9.q, Point.L3P10.q, Point.L3P11.q, Point.L3P12.q, Point.L3P13.q, Point.L3P14.q, Point.L3P15.q, Point.L3P16.q, Point.L3P17.q, Point.L3P18.q, Point.L3P19.q, Point.L3P20.q, Point.L3P21.q, Point.L3P22.q, Point.L3P23.q, Point.L3P24.q, Point.L3P25.q, Point.L3P26.q, Point.L3P27.q, Point.L3P28.q, Point.L3P29.q, Point.L3P30.q, Point.L3P31.q]
def ca : List (List PRO.Iv) := [Point.L3P0.a, Point.L3P1.a, Point.L3P2.a, Point.L3P3.a, Point.L3P4.a, Point.L3P5.a, Point.L3P6.a, Point.L3P7.a, Point.L3P8.a, Point.L3P9.a, Point.L3P10.a, Point.L3P11.a, Point.L3P12.a, Point.L3P13.a, Point.L3P14.a, Point.L3P15.a, Point.L3P16.a, Point.L3P17.a, Point.L3P18.a, Point.L3P19.a, Point.L3P20.a, Point.L3P21.a, Point.L3P22.a, Point.L3P23.a, Point.L3P24.a, Point.L3P25.a, Point.L3P26.a, Point.L3P27.a, Point.L3P28.a, Point.L3P29.a, Point.L3P30.a, Point.L3P31.a]
def ch : List (List PRO.Iv) := [Point.L3P0.h, Point.L3P1.h, Point.L3P2.h, Point.L3P3.h, Point.L3P4.h, Point.L3P5.h, Point.L3P6.h, Point.L3P7.h, Point.L3P8.h, Point.L3P9.h, Point.L3P10.h, Point.L3P11.h, Point.L3P12.h, Point.L3P13.h, Point.L3P14.h, Point.L3P15.h, Point.L3P16.h, Point.L3P17.h, Point.L3P18.h, Point.L3P19.h, Point.L3P20.h, Point.L3P21.h, Point.L3P22.h, Point.L3P23.h, Point.L3P24.h, Point.L3P25.h, Point.L3P26.h, Point.L3P27.h, Point.L3P28.h, Point.L3P29.h, Point.L3P30.h, Point.L3P31.h]
def co : List (List PRO.Iv) := [Point.L3P0.o, Point.L3P1.o, Point.L3P2.o, Point.L3P3.o, Point.L3P4.o, Point.L3P5.o, Point.L3P6.o, Point.L3P7.o, Point.L3P8.o, Point.L3P9.o, Point.L3P10.o, Point.L3P11.o, Point.L3P12.o, Point.L3P13.o, Point.L3P14.o, Point.L3P15.o, Point.L3P16.o, Point.L3P17.o, Point.L3P18.o, Point.L3P19.o, Point.L3P20.o, Point.L3P21.o, Point.L3P22.o, Point.L3P23.o, Point.L3P24.o, Point.L3P25.o, Point.L3P26.o, Point.L3P27.o, Point.L3P28.o, Point.L3P29.o, Point.L3P30.o, Point.L3P31.o]
theorem cx_rows : ∀ X ∈ cx, X.length = 128 := by decide +kernel
theorem co_valid : ∀ X ∈ co, ∀ B ∈ X, B.ok = true := by decide +kernel
def wx : List (List PRO.Iv) := [Point.L3P0.x, Point.L3P1.x, Point.L3P2.x, Point.L3P3.x, Point.L3P4.x, Point.L3P5.x, Point.L3P6.x, Point.L3P7.x, Point.L3P8.x, Point.L3P9.x, Point.L3P10.x, Point.L3P11.x, Point.L3P12.x, Point.L3P13.x, Point.L3P14.x, Point.L3P15.x, Point.L3P16.x, Point.L3P17.x, Point.L3P18.x, Point.L3P19.x, Point.L3P20.x, Point.L3P21.x, Point.L3P22.x, Point.L3P23.x, Point.L3P24.x, Point.L3P25.x, Point.L3P26.x, Point.L3P27.x, Point.L3P28.x, Point.L3P29.x, Point.L3P30.x, Point.L3P32.x]
def wq : List (List PRO.Iv) := [Point.L3P0.q, Point.L3P1.q, Point.L3P2.q, Point.L3P3.q, Point.L3P4.q, Point.L3P5.q, Point.L3P6.q, Point.L3P7.q, Point.L3P8.q, Point.L3P9.q, Point.L3P10.q, Point.L3P11.q, Point.L3P12.q, Point.L3P13.q, Point.L3P14.q, Point.L3P15.q, Point.L3P16.q, Point.L3P17.q, Point.L3P18.q, Point.L3P19.q, Point.L3P20.q, Point.L3P21.q, Point.L3P22.q, Point.L3P23.q, Point.L3P24.q, Point.L3P25.q, Point.L3P26.q, Point.L3P27.q, Point.L3P28.q, Point.L3P29.q, Point.L3P30.q, Point.L3P32.q]
def wa : List (List PRO.Iv) := [Point.L3P0.a, Point.L3P1.a, Point.L3P2.a, Point.L3P3.a, Point.L3P4.a, Point.L3P5.a, Point.L3P6.a, Point.L3P7.a, Point.L3P8.a, Point.L3P9.a, Point.L3P10.a, Point.L3P11.a, Point.L3P12.a, Point.L3P13.a, Point.L3P14.a, Point.L3P15.a, Point.L3P16.a, Point.L3P17.a, Point.L3P18.a, Point.L3P19.a, Point.L3P20.a, Point.L3P21.a, Point.L3P22.a, Point.L3P23.a, Point.L3P24.a, Point.L3P25.a, Point.L3P26.a, Point.L3P27.a, Point.L3P28.a, Point.L3P29.a, Point.L3P30.a, Point.L3P32.a]
def wh : List (List PRO.Iv) := [Point.L3P0.h, Point.L3P1.h, Point.L3P2.h, Point.L3P3.h, Point.L3P4.h, Point.L3P5.h, Point.L3P6.h, Point.L3P7.h, Point.L3P8.h, Point.L3P9.h, Point.L3P10.h, Point.L3P11.h, Point.L3P12.h, Point.L3P13.h, Point.L3P14.h, Point.L3P15.h, Point.L3P16.h, Point.L3P17.h, Point.L3P18.h, Point.L3P19.h, Point.L3P20.h, Point.L3P21.h, Point.L3P22.h, Point.L3P23.h, Point.L3P24.h, Point.L3P25.h, Point.L3P26.h, Point.L3P27.h, Point.L3P28.h, Point.L3P29.h, Point.L3P30.h, Point.L3P32.h]
def wo : List (List PRO.Iv) := [Point.L3P0.o, Point.L3P1.o, Point.L3P2.o, Point.L3P3.o, Point.L3P4.o, Point.L3P5.o, Point.L3P6.o, Point.L3P7.o, Point.L3P8.o, Point.L3P9.o, Point.L3P10.o, Point.L3P11.o, Point.L3P12.o, Point.L3P13.o, Point.L3P14.o, Point.L3P15.o, Point.L3P16.o, Point.L3P17.o, Point.L3P18.o, Point.L3P19.o, Point.L3P20.o, Point.L3P21.o, Point.L3P22.o, Point.L3P23.o, Point.L3P24.o, Point.L3P25.o, Point.L3P26.o, Point.L3P27.o, Point.L3P28.o, Point.L3P29.o, Point.L3P30.o, Point.L3P32.o]
theorem wx_rows : ∀ X ∈ wx, X.length = 128 := by decide +kernel
theorem wo_valid : ∀ X ∈ wo, ∀ B ∈ X, B.ok = true := by decide +kernel
theorem decode : CompletionBridge.decodeLayer (PRO.LL 3) = CON.layer3 := by
  simp only [CON.layer3, mat_eq, row_eq_vec]
  rfl
theorem qkv_rows : (PRO.LL 3).qkvW.length = 384 := by decide +kernel
end PythiaCert.Frame.L3
