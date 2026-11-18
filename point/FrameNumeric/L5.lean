import FrameData.L5
import PointChecks.L5.P0Q
import PointChecks.L5.P1Q
import PointChecks.L5.P2Q
import PointChecks.L5.P3Q
import PointChecks.L5.P4Q
import PointChecks.L5.P5Q
import PointChecks.L5.P6Q
import PointChecks.L5.P7Q
import PointChecks.L5.P8Q
import PointChecks.L5.P9Q
import PointChecks.L5.P10Q
import PointChecks.L5.P11Q
import PointChecks.L5.P12Q
import PointChecks.L5.P13Q
import PointChecks.L5.P14Q
import PointChecks.L5.P15Q
import PointChecks.L5.P16Q
import PointChecks.L5.P17Q
import PointChecks.L5.P18Q
import PointChecks.L5.P19Q
import PointChecks.L5.P20Q
import PointChecks.L5.P21Q
import PointChecks.L5.P22Q
import PointChecks.L5.P23Q
import PointChecks.L5.P24Q
import PointChecks.L5.P25Q
import PointChecks.L5.P26Q
import PointChecks.L5.P27Q
import PointChecks.L5.P28Q
import PointChecks.L5.P29Q
import PointChecks.L5.P30Q
import PointChecks.L5.P31Q
import PointChecks.L5.P31A
import PointChecks.L5.P31H
import PointChecks.L5.P31O
import PointChecks.L5.P32Q
import PointChecks.L5.P32A
import PointChecks.L5.P32H
import PointChecks.L5.P32O
namespace PythiaCert.Frame.L5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cq_checks : ∀ i, i < cx.length → PRO.qCheck (PRO.LL 5) (cx.getD i []) (cq.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L5P0.q_check
  · exact Point.L5P1.q_check
  · exact Point.L5P2.q_check
  · exact Point.L5P3.q_check
  · exact Point.L5P4.q_check
  · exact Point.L5P5.q_check
  · exact Point.L5P6.q_check
  · exact Point.L5P7.q_check
  · exact Point.L5P8.q_check
  · exact Point.L5P9.q_check
  · exact Point.L5P10.q_check
  · exact Point.L5P11.q_check
  · exact Point.L5P12.q_check
  · exact Point.L5P13.q_check
  · exact Point.L5P14.q_check
  · exact Point.L5P15.q_check
  · exact Point.L5P16.q_check
  · exact Point.L5P17.q_check
  · exact Point.L5P18.q_check
  · exact Point.L5P19.q_check
  · exact Point.L5P20.q_check
  · exact Point.L5P21.q_check
  · exact Point.L5P22.q_check
  · exact Point.L5P23.q_check
  · exact Point.L5P24.q_check
  · exact Point.L5P25.q_check
  · exact Point.L5P26.q_check
  · exact Point.L5P27.q_check
  · exact Point.L5P28.q_check
  · exact Point.L5P29.q_check
  · exact Point.L5P30.q_check
  · exact Point.L5P31.q_check
theorem wq_checks : ∀ i, i < wx.length → PRO.qCheck (PRO.LL 5) (wx.getD i []) (wq.getD i []) = true := by
  intro i hi
  have hi32 : i < 32 := hi
  interval_cases i
  · exact Point.L5P0.q_check
  · exact Point.L5P1.q_check
  · exact Point.L5P2.q_check
  · exact Point.L5P3.q_check
  · exact Point.L5P4.q_check
  · exact Point.L5P5.q_check
  · exact Point.L5P6.q_check
  · exact Point.L5P7.q_check
  · exact Point.L5P8.q_check
  · exact Point.L5P9.q_check
  · exact Point.L5P10.q_check
  · exact Point.L5P11.q_check
  · exact Point.L5P12.q_check
  · exact Point.L5P13.q_check
  · exact Point.L5P14.q_check
  · exact Point.L5P15.q_check
  · exact Point.L5P16.q_check
  · exact Point.L5P17.q_check
  · exact Point.L5P18.q_check
  · exact Point.L5P19.q_check
  · exact Point.L5P20.q_check
  · exact Point.L5P21.q_check
  · exact Point.L5P22.q_check
  · exact Point.L5P23.q_check
  · exact Point.L5P24.q_check
  · exact Point.L5P25.q_check
  · exact Point.L5P26.q_check
  · exact Point.L5P27.q_check
  · exact Point.L5P28.q_check
  · exact Point.L5P29.q_check
  · exact Point.L5P30.q_check
  · exact Point.L5P32.q_check
end PythiaCert.Frame.L5
