import PointData.L5.P0
import PointData.L5.P1
import PointData.L5.P2
import PointData.L5.P3
import PointData.L5.P4
import PointData.L5.P5
import PointData.L5.P6
import PointData.L5.P7
import PointData.L5.P8
import PointData.L5.P9
import PointData.L5.P10
import PointData.L5.P11
import PointData.L5.P12
import PointData.L5.P13
import PointData.L5.P14
import PointData.L5.P15
import PointData.L5.P16
import PointData.L5.P17
import PointData.L5.P18
import PointData.L5.P19
import PointData.L5.P20
import PointData.L5.P21
import PointData.L5.P22
import PointData.L5.P23
import PointData.L5.P24
import PointData.L5.P25
import PointData.L5.P26
import PointData.L5.P27
import PointData.L5.P28
import PointData.L5.P29
import PointData.L5.P30
import PointData.L5.P31
import PointData.L5.P32
import FrameSound
namespace PythiaCert.Frame.L5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cx : List (List PRO.Iv) := [Point.L5P0.x, Point.L5P1.x, Point.L5P2.x, Point.L5P3.x, Point.L5P4.x, Point.L5P5.x, Point.L5P6.x, Point.L5P7.x, Point.L5P8.x, Point.L5P9.x, Point.L5P10.x, Point.L5P11.x, Point.L5P12.x, Point.L5P13.x, Point.L5P14.x, Point.L5P15.x, Point.L5P16.x, Point.L5P17.x, Point.L5P18.x, Point.L5P19.x, Point.L5P20.x, Point.L5P21.x, Point.L5P22.x, Point.L5P23.x, Point.L5P24.x, Point.L5P25.x, Point.L5P26.x, Point.L5P27.x, Point.L5P28.x, Point.L5P29.x, Point.L5P30.x, Point.L5P31.x]
def cq : List (List PRO.Iv) := [Point.L5P0.q, Point.L5P1.q, Point.L5P2.q, Point.L5P3.q, Point.L5P4.q, Point.L5P5.q, Point.L5P6.q, Point.L5P7.q, Point.L5P8.q, Point.L5P9.q, Point.L5P10.q, Point.L5P11.q, Point.L5P12.q, Point.L5P13.q, Point.L5P14.q, Point.L5P15.q, Point.L5P16.q, Point.L5P17.q, Point.L5P18.q, Point.L5P19.q, Point.L5P20.q, Point.L5P21.q, Point.L5P22.q, Point.L5P23.q, Point.L5P24.q, Point.L5P25.q, Point.L5P26.q, Point.L5P27.q, Point.L5P28.q, Point.L5P29.q, Point.L5P30.q, Point.L5P31.q]
def ca : List (List PRO.Iv) := [Point.L5P0.a, Point.L5P1.a, Point.L5P2.a, Point.L5P3.a, Point.L5P4.a, Point.L5P5.a, Point.L5P6.a, Point.L5P7.a, Point.L5P8.a, Point.L5P9.a, Point.L5P10.a, Point.L5P11.a, Point.L5P12.a, Point.L5P13.a, Point.L5P14.a, Point.L5P15.a, Point.L5P16.a, Point.L5P17.a, Point.L5P18.a, Point.L5P19.a, Point.L5P20.a, Point.L5P21.a, Point.L5P22.a, Point.L5P23.a, Point.L5P24.a, Point.L5P25.a, Point.L5P26.a, Point.L5P27.a, Point.L5P28.a, Point.L5P29.a, Point.L5P30.a, Point.L5P31.a]
def ch : List (List PRO.Iv) := [Point.L5P0.h, Point.L5P1.h, Point.L5P2.h, Point.L5P3.h, Point.L5P4.h, Point.L5P5.h, Point.L5P6.h, Point.L5P7.h, Point.L5P8.h, Point.L5P9.h, Point.L5P10.h, Point.L5P11.h, Point.L5P12.h, Point.L5P13.h, Point.L5P14.h, Point.L5P15.h, Point.L5P16.h, Point.L5P17.h, Point.L5P18.h, Point.L5P19.h, Point.L5P20.h, Point.L5P21.h, Point.L5P22.h, Point.L5P23.h, Point.L5P24.h, Point.L5P25.h, Point.L5P26.h, Point.L5P27.h, Point.L5P28.h, Point.L5P29.h, Point.L5P30.h, Point.L5P31.h]
def co : List (List PRO.Iv) := [Point.L5P0.o, Point.L5P1.o, Point.L5P2.o, Point.L5P3.o, Point.L5P4.o, Point.L5P5.o, Point.L5P6.o, Point.L5P7.o, Point.L5P8.o, Point.L5P9.o, Point.L5P10.o, Point.L5P11.o, Point.L5P12.o, Point.L5P13.o, Point.L5P14.o, Point.L5P15.o, Point.L5P16.o, Point.L5P17.o, Point.L5P18.o, Point.L5P19.o, Point.L5P20.o, Point.L5P21.o, Point.L5P22.o, Point.L5P23.o, Point.L5P24.o, Point.L5P25.o, Point.L5P26.o, Point.L5P27.o, Point.L5P28.o, Point.L5P29.o, Point.L5P30.o, Point.L5P31.o]
theorem cx_rows : ∀ X ∈ cx, X.length = 128 := by decide +kernel
theorem co_valid : ∀ X ∈ co, ∀ B ∈ X, B.ok = true := by decide +kernel
def wx : List (List PRO.Iv) := [Point.L5P0.x, Point.L5P1.x, Point.L5P2.x, Point.L5P3.x, Point.L5P4.x, Point.L5P5.x, Point.L5P6.x, Point.L5P7.x, Point.L5P8.x, Point.L5P9.x, Point.L5P10.x, Point.L5P11.x, Point.L5P12.x, Point.L5P13.x, Point.L5P14.x, Point.L5P15.x, Point.L5P16.x, Point.L5P17.x, Point.L5P18.x, Point.L5P19.x, Point.L5P20.x, Point.L5P21.x, Point.L5P22.x, Point.L5P23.x, Point.L5P24.x, Point.L5P25.x, Point.L5P26.x, Point.L5P27.x, Point.L5P28.x, Point.L5P29.x, Point.L5P30.x, Point.L5P32.x]
def wq : List (List PRO.Iv) := [Point.L5P0.q, Point.L5P1.q, Point.L5P2.q, Point.L5P3.q, Point.L5P4.q, Point.L5P5.q, Point.L5P6.q, Point.L5P7.q, Point.L5P8.q, Point.L5P9.q, Point.L5P10.q, Point.L5P11.q, Point.L5P12.q, Point.L5P13.q, Point.L5P14.q, Point.L5P15.q, Point.L5P16.q, Point.L5P17.q, Point.L5P18.q, Point.L5P19.q, Point.L5P20.q, Point.L5P21.q, Point.L5P22.q, Point.L5P23.q, Point.L5P24.q, Point.L5P25.q, Point.L5P26.q, Point.L5P27.q, Point.L5P28.q, Point.L5P29.q, Point.L5P30.q, Point.L5P32.q]
def wa : List (List PRO.Iv) := [Point.L5P0.a, Point.L5P1.a, Point.L5P2.a, Point.L5P3.a, Point.L5P4.a, Point.L5P5.a, Point.L5P6.a, Point.L5P7.a, Point.L5P8.a, Point.L5P9.a, Point.L5P10.a, Point.L5P11.a, Point.L5P12.a, Point.L5P13.a, Point.L5P14.a, Point.L5P15.a, Point.L5P16.a, Point.L5P17.a, Point.L5P18.a, Point.L5P19.a, Point.L5P20.a, Point.L5P21.a, Point.L5P22.a, Point.L5P23.a, Point.L5P24.a, Point.L5P25.a, Point.L5P26.a, Point.L5P27.a, Point.L5P28.a, Point.L5P29.a, Point.L5P30.a, Point.L5P32.a]
def wh : List (List PRO.Iv) := [Point.L5P0.h, Point.L5P1.h, Point.L5P2.h, Point.L5P3.h, Point.L5P4.h, Point.L5P5.h, Point.L5P6.h, Point.L5P7.h, Point.L5P8.h, Point.L5P9.h, Point.L5P10.h, Point.L5P11.h, Point.L5P12.h, Point.L5P13.h, Point.L5P14.h, Point.L5P15.h, Point.L5P16.h, Point.L5P17.h, Point.L5P18.h, Point.L5P19.h, Point.L5P20.h, Point.L5P21.h, Point.L5P22.h, Point.L5P23.h, Point.L5P24.h, Point.L5P25.h, Point.L5P26.h, Point.L5P27.h, Point.L5P28.h, Point.L5P29.h, Point.L5P30.h, Point.L5P32.h]
def wo : List (List PRO.Iv) := [Point.L5P0.o, Point.L5P1.o, Point.L5P2.o, Point.L5P3.o, Point.L5P4.o, Point.L5P5.o, Point.L5P6.o, Point.L5P7.o, Point.L5P8.o, Point.L5P9.o, Point.L5P10.o, Point.L5P11.o, Point.L5P12.o, Point.L5P13.o, Point.L5P14.o, Point.L5P15.o, Point.L5P16.o, Point.L5P17.o, Point.L5P18.o, Point.L5P19.o, Point.L5P20.o, Point.L5P21.o, Point.L5P22.o, Point.L5P23.o, Point.L5P24.o, Point.L5P25.o, Point.L5P26.o, Point.L5P27.o, Point.L5P28.o, Point.L5P29.o, Point.L5P30.o, Point.L5P32.o]
theorem wx_rows : ∀ X ∈ wx, X.length = 128 := by decide +kernel
theorem wo_valid : ∀ X ∈ wo, ∀ B ∈ X, B.ok = true := by decide +kernel
theorem decode : CompletionBridge.decodeLayer (PRO.LL 5) = CON.layer5 := by
  simp only [CON.layer5, mat_eq, row_eq_vec]
  rfl
theorem qkv_rows : (PRO.LL 5).qkvW.length = 384 := by decide +kernel
end PythiaCert.Frame.L5
