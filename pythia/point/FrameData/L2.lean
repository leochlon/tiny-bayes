import PointData.L2.P0
import PointData.L2.P1
import PointData.L2.P2
import PointData.L2.P3
import PointData.L2.P4
import PointData.L2.P5
import PointData.L2.P6
import PointData.L2.P7
import PointData.L2.P8
import PointData.L2.P9
import PointData.L2.P10
import PointData.L2.P11
import PointData.L2.P12
import PointData.L2.P13
import PointData.L2.P14
import PointData.L2.P15
import PointData.L2.P16
import PointData.L2.P17
import PointData.L2.P18
import PointData.L2.P19
import PointData.L2.P20
import PointData.L2.P21
import PointData.L2.P22
import PointData.L2.P23
import PointData.L2.P24
import PointData.L2.P25
import PointData.L2.P26
import PointData.L2.P27
import PointData.L2.P28
import PointData.L2.P29
import PointData.L2.P30
import PointData.L2.P31
import PointData.L2.P32
import FrameSound
namespace PythiaCert.Frame.L2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cx : List (List PRO.Iv) := [Point.L2P0.x, Point.L2P1.x, Point.L2P2.x, Point.L2P3.x, Point.L2P4.x, Point.L2P5.x, Point.L2P6.x, Point.L2P7.x, Point.L2P8.x, Point.L2P9.x, Point.L2P10.x, Point.L2P11.x, Point.L2P12.x, Point.L2P13.x, Point.L2P14.x, Point.L2P15.x, Point.L2P16.x, Point.L2P17.x, Point.L2P18.x, Point.L2P19.x, Point.L2P20.x, Point.L2P21.x, Point.L2P22.x, Point.L2P23.x, Point.L2P24.x, Point.L2P25.x, Point.L2P26.x, Point.L2P27.x, Point.L2P28.x, Point.L2P29.x, Point.L2P30.x, Point.L2P31.x]
def cq : List (List PRO.Iv) := [Point.L2P0.q, Point.L2P1.q, Point.L2P2.q, Point.L2P3.q, Point.L2P4.q, Point.L2P5.q, Point.L2P6.q, Point.L2P7.q, Point.L2P8.q, Point.L2P9.q, Point.L2P10.q, Point.L2P11.q, Point.L2P12.q, Point.L2P13.q, Point.L2P14.q, Point.L2P15.q, Point.L2P16.q, Point.L2P17.q, Point.L2P18.q, Point.L2P19.q, Point.L2P20.q, Point.L2P21.q, Point.L2P22.q, Point.L2P23.q, Point.L2P24.q, Point.L2P25.q, Point.L2P26.q, Point.L2P27.q, Point.L2P28.q, Point.L2P29.q, Point.L2P30.q, Point.L2P31.q]
def ca : List (List PRO.Iv) := [Point.L2P0.a, Point.L2P1.a, Point.L2P2.a, Point.L2P3.a, Point.L2P4.a, Point.L2P5.a, Point.L2P6.a, Point.L2P7.a, Point.L2P8.a, Point.L2P9.a, Point.L2P10.a, Point.L2P11.a, Point.L2P12.a, Point.L2P13.a, Point.L2P14.a, Point.L2P15.a, Point.L2P16.a, Point.L2P17.a, Point.L2P18.a, Point.L2P19.a, Point.L2P20.a, Point.L2P21.a, Point.L2P22.a, Point.L2P23.a, Point.L2P24.a, Point.L2P25.a, Point.L2P26.a, Point.L2P27.a, Point.L2P28.a, Point.L2P29.a, Point.L2P30.a, Point.L2P31.a]
def ch : List (List PRO.Iv) := [Point.L2P0.h, Point.L2P1.h, Point.L2P2.h, Point.L2P3.h, Point.L2P4.h, Point.L2P5.h, Point.L2P6.h, Point.L2P7.h, Point.L2P8.h, Point.L2P9.h, Point.L2P10.h, Point.L2P11.h, Point.L2P12.h, Point.L2P13.h, Point.L2P14.h, Point.L2P15.h, Point.L2P16.h, Point.L2P17.h, Point.L2P18.h, Point.L2P19.h, Point.L2P20.h, Point.L2P21.h, Point.L2P22.h, Point.L2P23.h, Point.L2P24.h, Point.L2P25.h, Point.L2P26.h, Point.L2P27.h, Point.L2P28.h, Point.L2P29.h, Point.L2P30.h, Point.L2P31.h]
def co : List (List PRO.Iv) := [Point.L2P0.o, Point.L2P1.o, Point.L2P2.o, Point.L2P3.o, Point.L2P4.o, Point.L2P5.o, Point.L2P6.o, Point.L2P7.o, Point.L2P8.o, Point.L2P9.o, Point.L2P10.o, Point.L2P11.o, Point.L2P12.o, Point.L2P13.o, Point.L2P14.o, Point.L2P15.o, Point.L2P16.o, Point.L2P17.o, Point.L2P18.o, Point.L2P19.o, Point.L2P20.o, Point.L2P21.o, Point.L2P22.o, Point.L2P23.o, Point.L2P24.o, Point.L2P25.o, Point.L2P26.o, Point.L2P27.o, Point.L2P28.o, Point.L2P29.o, Point.L2P30.o, Point.L2P31.o]
theorem cx_rows : ∀ X ∈ cx, X.length = 128 := by decide +kernel
theorem co_valid : ∀ X ∈ co, ∀ B ∈ X, B.ok = true := by decide +kernel
def wx : List (List PRO.Iv) := [Point.L2P0.x, Point.L2P1.x, Point.L2P2.x, Point.L2P3.x, Point.L2P4.x, Point.L2P5.x, Point.L2P6.x, Point.L2P7.x, Point.L2P8.x, Point.L2P9.x, Point.L2P10.x, Point.L2P11.x, Point.L2P12.x, Point.L2P13.x, Point.L2P14.x, Point.L2P15.x, Point.L2P16.x, Point.L2P17.x, Point.L2P18.x, Point.L2P19.x, Point.L2P20.x, Point.L2P21.x, Point.L2P22.x, Point.L2P23.x, Point.L2P24.x, Point.L2P25.x, Point.L2P26.x, Point.L2P27.x, Point.L2P28.x, Point.L2P29.x, Point.L2P30.x, Point.L2P32.x]
def wq : List (List PRO.Iv) := [Point.L2P0.q, Point.L2P1.q, Point.L2P2.q, Point.L2P3.q, Point.L2P4.q, Point.L2P5.q, Point.L2P6.q, Point.L2P7.q, Point.L2P8.q, Point.L2P9.q, Point.L2P10.q, Point.L2P11.q, Point.L2P12.q, Point.L2P13.q, Point.L2P14.q, Point.L2P15.q, Point.L2P16.q, Point.L2P17.q, Point.L2P18.q, Point.L2P19.q, Point.L2P20.q, Point.L2P21.q, Point.L2P22.q, Point.L2P23.q, Point.L2P24.q, Point.L2P25.q, Point.L2P26.q, Point.L2P27.q, Point.L2P28.q, Point.L2P29.q, Point.L2P30.q, Point.L2P32.q]
def wa : List (List PRO.Iv) := [Point.L2P0.a, Point.L2P1.a, Point.L2P2.a, Point.L2P3.a, Point.L2P4.a, Point.L2P5.a, Point.L2P6.a, Point.L2P7.a, Point.L2P8.a, Point.L2P9.a, Point.L2P10.a, Point.L2P11.a, Point.L2P12.a, Point.L2P13.a, Point.L2P14.a, Point.L2P15.a, Point.L2P16.a, Point.L2P17.a, Point.L2P18.a, Point.L2P19.a, Point.L2P20.a, Point.L2P21.a, Point.L2P22.a, Point.L2P23.a, Point.L2P24.a, Point.L2P25.a, Point.L2P26.a, Point.L2P27.a, Point.L2P28.a, Point.L2P29.a, Point.L2P30.a, Point.L2P32.a]
def wh : List (List PRO.Iv) := [Point.L2P0.h, Point.L2P1.h, Point.L2P2.h, Point.L2P3.h, Point.L2P4.h, Point.L2P5.h, Point.L2P6.h, Point.L2P7.h, Point.L2P8.h, Point.L2P9.h, Point.L2P10.h, Point.L2P11.h, Point.L2P12.h, Point.L2P13.h, Point.L2P14.h, Point.L2P15.h, Point.L2P16.h, Point.L2P17.h, Point.L2P18.h, Point.L2P19.h, Point.L2P20.h, Point.L2P21.h, Point.L2P22.h, Point.L2P23.h, Point.L2P24.h, Point.L2P25.h, Point.L2P26.h, Point.L2P27.h, Point.L2P28.h, Point.L2P29.h, Point.L2P30.h, Point.L2P32.h]
def wo : List (List PRO.Iv) := [Point.L2P0.o, Point.L2P1.o, Point.L2P2.o, Point.L2P3.o, Point.L2P4.o, Point.L2P5.o, Point.L2P6.o, Point.L2P7.o, Point.L2P8.o, Point.L2P9.o, Point.L2P10.o, Point.L2P11.o, Point.L2P12.o, Point.L2P13.o, Point.L2P14.o, Point.L2P15.o, Point.L2P16.o, Point.L2P17.o, Point.L2P18.o, Point.L2P19.o, Point.L2P20.o, Point.L2P21.o, Point.L2P22.o, Point.L2P23.o, Point.L2P24.o, Point.L2P25.o, Point.L2P26.o, Point.L2P27.o, Point.L2P28.o, Point.L2P29.o, Point.L2P30.o, Point.L2P32.o]
theorem wx_rows : ∀ X ∈ wx, X.length = 128 := by decide +kernel
theorem wo_valid : ∀ X ∈ wo, ∀ B ∈ X, B.ok = true := by decide +kernel
theorem decode : CompletionBridge.decodeLayer (PRO.LL 2) = CON.layer2 := by
  simp only [CON.layer2, mat_eq, row_eq_vec]
  rfl
theorem qkv_rows : (PRO.LL 2).qkvW.length = 384 := by decide +kernel
end PythiaCert.Frame.L2
