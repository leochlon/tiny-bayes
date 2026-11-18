import PointData.L4.P0
import PointData.L4.P1
import PointData.L4.P2
import PointData.L4.P3
import PointData.L4.P4
import PointData.L4.P5
import PointData.L4.P6
import PointData.L4.P7
import PointData.L4.P8
import PointData.L4.P9
import PointData.L4.P10
import PointData.L4.P11
import PointData.L4.P12
import PointData.L4.P13
import PointData.L4.P14
import PointData.L4.P15
import PointData.L4.P16
import PointData.L4.P17
import PointData.L4.P18
import PointData.L4.P19
import PointData.L4.P20
import PointData.L4.P21
import PointData.L4.P22
import PointData.L4.P23
import PointData.L4.P24
import PointData.L4.P25
import PointData.L4.P26
import PointData.L4.P27
import PointData.L4.P28
import PointData.L4.P29
import PointData.L4.P30
import PointData.L4.P31
import PointData.L4.P32
import FrameSound
namespace PythiaCert.Frame.L4
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cx : List (List PRO.Iv) := [Point.L4P0.x, Point.L4P1.x, Point.L4P2.x, Point.L4P3.x, Point.L4P4.x, Point.L4P5.x, Point.L4P6.x, Point.L4P7.x, Point.L4P8.x, Point.L4P9.x, Point.L4P10.x, Point.L4P11.x, Point.L4P12.x, Point.L4P13.x, Point.L4P14.x, Point.L4P15.x, Point.L4P16.x, Point.L4P17.x, Point.L4P18.x, Point.L4P19.x, Point.L4P20.x, Point.L4P21.x, Point.L4P22.x, Point.L4P23.x, Point.L4P24.x, Point.L4P25.x, Point.L4P26.x, Point.L4P27.x, Point.L4P28.x, Point.L4P29.x, Point.L4P30.x, Point.L4P31.x]
def cq : List (List PRO.Iv) := [Point.L4P0.q, Point.L4P1.q, Point.L4P2.q, Point.L4P3.q, Point.L4P4.q, Point.L4P5.q, Point.L4P6.q, Point.L4P7.q, Point.L4P8.q, Point.L4P9.q, Point.L4P10.q, Point.L4P11.q, Point.L4P12.q, Point.L4P13.q, Point.L4P14.q, Point.L4P15.q, Point.L4P16.q, Point.L4P17.q, Point.L4P18.q, Point.L4P19.q, Point.L4P20.q, Point.L4P21.q, Point.L4P22.q, Point.L4P23.q, Point.L4P24.q, Point.L4P25.q, Point.L4P26.q, Point.L4P27.q, Point.L4P28.q, Point.L4P29.q, Point.L4P30.q, Point.L4P31.q]
def ca : List (List PRO.Iv) := [Point.L4P0.a, Point.L4P1.a, Point.L4P2.a, Point.L4P3.a, Point.L4P4.a, Point.L4P5.a, Point.L4P6.a, Point.L4P7.a, Point.L4P8.a, Point.L4P9.a, Point.L4P10.a, Point.L4P11.a, Point.L4P12.a, Point.L4P13.a, Point.L4P14.a, Point.L4P15.a, Point.L4P16.a, Point.L4P17.a, Point.L4P18.a, Point.L4P19.a, Point.L4P20.a, Point.L4P21.a, Point.L4P22.a, Point.L4P23.a, Point.L4P24.a, Point.L4P25.a, Point.L4P26.a, Point.L4P27.a, Point.L4P28.a, Point.L4P29.a, Point.L4P30.a, Point.L4P31.a]
def ch : List (List PRO.Iv) := [Point.L4P0.h, Point.L4P1.h, Point.L4P2.h, Point.L4P3.h, Point.L4P4.h, Point.L4P5.h, Point.L4P6.h, Point.L4P7.h, Point.L4P8.h, Point.L4P9.h, Point.L4P10.h, Point.L4P11.h, Point.L4P12.h, Point.L4P13.h, Point.L4P14.h, Point.L4P15.h, Point.L4P16.h, Point.L4P17.h, Point.L4P18.h, Point.L4P19.h, Point.L4P20.h, Point.L4P21.h, Point.L4P22.h, Point.L4P23.h, Point.L4P24.h, Point.L4P25.h, Point.L4P26.h, Point.L4P27.h, Point.L4P28.h, Point.L4P29.h, Point.L4P30.h, Point.L4P31.h]
def co : List (List PRO.Iv) := [Point.L4P0.o, Point.L4P1.o, Point.L4P2.o, Point.L4P3.o, Point.L4P4.o, Point.L4P5.o, Point.L4P6.o, Point.L4P7.o, Point.L4P8.o, Point.L4P9.o, Point.L4P10.o, Point.L4P11.o, Point.L4P12.o, Point.L4P13.o, Point.L4P14.o, Point.L4P15.o, Point.L4P16.o, Point.L4P17.o, Point.L4P18.o, Point.L4P19.o, Point.L4P20.o, Point.L4P21.o, Point.L4P22.o, Point.L4P23.o, Point.L4P24.o, Point.L4P25.o, Point.L4P26.o, Point.L4P27.o, Point.L4P28.o, Point.L4P29.o, Point.L4P30.o, Point.L4P31.o]
theorem cx_rows : ∀ X ∈ cx, X.length = 128 := by decide +kernel
theorem co_valid : ∀ X ∈ co, ∀ B ∈ X, B.ok = true := by decide +kernel
def wx : List (List PRO.Iv) := [Point.L4P0.x, Point.L4P1.x, Point.L4P2.x, Point.L4P3.x, Point.L4P4.x, Point.L4P5.x, Point.L4P6.x, Point.L4P7.x, Point.L4P8.x, Point.L4P9.x, Point.L4P10.x, Point.L4P11.x, Point.L4P12.x, Point.L4P13.x, Point.L4P14.x, Point.L4P15.x, Point.L4P16.x, Point.L4P17.x, Point.L4P18.x, Point.L4P19.x, Point.L4P20.x, Point.L4P21.x, Point.L4P22.x, Point.L4P23.x, Point.L4P24.x, Point.L4P25.x, Point.L4P26.x, Point.L4P27.x, Point.L4P28.x, Point.L4P29.x, Point.L4P30.x, Point.L4P32.x]
def wq : List (List PRO.Iv) := [Point.L4P0.q, Point.L4P1.q, Point.L4P2.q, Point.L4P3.q, Point.L4P4.q, Point.L4P5.q, Point.L4P6.q, Point.L4P7.q, Point.L4P8.q, Point.L4P9.q, Point.L4P10.q, Point.L4P11.q, Point.L4P12.q, Point.L4P13.q, Point.L4P14.q, Point.L4P15.q, Point.L4P16.q, Point.L4P17.q, Point.L4P18.q, Point.L4P19.q, Point.L4P20.q, Point.L4P21.q, Point.L4P22.q, Point.L4P23.q, Point.L4P24.q, Point.L4P25.q, Point.L4P26.q, Point.L4P27.q, Point.L4P28.q, Point.L4P29.q, Point.L4P30.q, Point.L4P32.q]
def wa : List (List PRO.Iv) := [Point.L4P0.a, Point.L4P1.a, Point.L4P2.a, Point.L4P3.a, Point.L4P4.a, Point.L4P5.a, Point.L4P6.a, Point.L4P7.a, Point.L4P8.a, Point.L4P9.a, Point.L4P10.a, Point.L4P11.a, Point.L4P12.a, Point.L4P13.a, Point.L4P14.a, Point.L4P15.a, Point.L4P16.a, Point.L4P17.a, Point.L4P18.a, Point.L4P19.a, Point.L4P20.a, Point.L4P21.a, Point.L4P22.a, Point.L4P23.a, Point.L4P24.a, Point.L4P25.a, Point.L4P26.a, Point.L4P27.a, Point.L4P28.a, Point.L4P29.a, Point.L4P30.a, Point.L4P32.a]
def wh : List (List PRO.Iv) := [Point.L4P0.h, Point.L4P1.h, Point.L4P2.h, Point.L4P3.h, Point.L4P4.h, Point.L4P5.h, Point.L4P6.h, Point.L4P7.h, Point.L4P8.h, Point.L4P9.h, Point.L4P10.h, Point.L4P11.h, Point.L4P12.h, Point.L4P13.h, Point.L4P14.h, Point.L4P15.h, Point.L4P16.h, Point.L4P17.h, Point.L4P18.h, Point.L4P19.h, Point.L4P20.h, Point.L4P21.h, Point.L4P22.h, Point.L4P23.h, Point.L4P24.h, Point.L4P25.h, Point.L4P26.h, Point.L4P27.h, Point.L4P28.h, Point.L4P29.h, Point.L4P30.h, Point.L4P32.h]
def wo : List (List PRO.Iv) := [Point.L4P0.o, Point.L4P1.o, Point.L4P2.o, Point.L4P3.o, Point.L4P4.o, Point.L4P5.o, Point.L4P6.o, Point.L4P7.o, Point.L4P8.o, Point.L4P9.o, Point.L4P10.o, Point.L4P11.o, Point.L4P12.o, Point.L4P13.o, Point.L4P14.o, Point.L4P15.o, Point.L4P16.o, Point.L4P17.o, Point.L4P18.o, Point.L4P19.o, Point.L4P20.o, Point.L4P21.o, Point.L4P22.o, Point.L4P23.o, Point.L4P24.o, Point.L4P25.o, Point.L4P26.o, Point.L4P27.o, Point.L4P28.o, Point.L4P29.o, Point.L4P30.o, Point.L4P32.o]
theorem wx_rows : ∀ X ∈ wx, X.length = 128 := by decide +kernel
theorem wo_valid : ∀ X ∈ wo, ∀ B ∈ X, B.ok = true := by decide +kernel
theorem decode : CompletionBridge.decodeLayer (PRO.LL 4) = CON.layer4 := by
  simp only [CON.layer4, mat_eq, row_eq_vec]
  rfl
theorem qkv_rows : (PRO.LL 4).qkvW.length = 384 := by decide +kernel
end PythiaCert.Frame.L4
