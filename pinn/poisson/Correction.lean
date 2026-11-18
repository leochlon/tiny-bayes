import HC33
import HC32
import HC31
import HC30
import HC23
import HC22
import HC21
import HC20
import HC13
import HC12
import HC11
import HC10
import HC0333
import HC0332
import HC0331
import HC03303
import HC03302
import HC03301
import HC033003
import HC033002
import HC033001
import HC033000
import HC0323
import HC0322
import HC03213
import HC03212
import HC03211
import HC03210
import HC0320
import HC031
import HC030
import HC02
import HC01
import HC00
namespace PoissonR3
open PoissonPilot
noncomputable section
set_option maxHeartbeats 0

theorem correction_bound (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |C x y| ≤ certA := by
  by_cases hxroot : x ≤ (1:ℝ)/2
  · by_cases hyroot : y ≤ (1:ℝ)/2
    · by_cases hx0 : x ≤ (1:ℝ)/4
      · by_cases hy0 : y ≤ (1:ℝ)/4
        · exact leaf00 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · exact leaf01 x y (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hy0 : y ≤ (1:ℝ)/4
        · exact leaf02 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · by_cases hx03 : x ≤ (3:ℝ)/8
          · by_cases hy03 : y ≤ (3:ℝ)/8
            · exact leaf030 x y (by linarith) (by linarith) (by linarith) (by linarith)
            · exact leaf031 x y (by linarith) (by linarith) (by linarith) (by linarith)
          · by_cases hy03 : y ≤ (3:ℝ)/8
            · by_cases hx032 : x ≤ (7:ℝ)/16
              · by_cases hy032 : y ≤ (5:ℝ)/16
                · exact leaf0320 x y (by linarith) (by linarith) (by linarith) (by linarith)
                · by_cases hx0321 : x ≤ (13:ℝ)/32
                  · by_cases hy0321 : y ≤ (11:ℝ)/32
                    · exact leaf03210 x y (by linarith) (by linarith) (by linarith) (by linarith)
                    · exact leaf03211 x y (by linarith) (by linarith) (by linarith) (by linarith)
                  · by_cases hy0321 : y ≤ (11:ℝ)/32
                    · exact leaf03212 x y (by linarith) (by linarith) (by linarith) (by linarith)
                    · exact leaf03213 x y (by linarith) (by linarith) (by linarith) (by linarith)
              · by_cases hy032 : y ≤ (5:ℝ)/16
                · exact leaf0322 x y (by linarith) (by linarith) (by linarith) (by linarith)
                · exact leaf0323 x y (by linarith) (by linarith) (by linarith) (by linarith)
            · by_cases hx033 : x ≤ (7:ℝ)/16
              · by_cases hy033 : y ≤ (7:ℝ)/16
                · by_cases hx0330 : x ≤ (13:ℝ)/32
                  · by_cases hy0330 : y ≤ (13:ℝ)/32
                    · by_cases hx03300 : x ≤ (25:ℝ)/64
                      · by_cases hy03300 : y ≤ (25:ℝ)/64
                        · exact leaf033000 x y (by linarith) (by linarith) (by linarith) (by linarith)
                        · exact leaf033001 x y (by linarith) (by linarith) (by linarith) (by linarith)
                      · by_cases hy03300 : y ≤ (25:ℝ)/64
                        · exact leaf033002 x y (by linarith) (by linarith) (by linarith) (by linarith)
                        · exact leaf033003 x y (by linarith) (by linarith) (by linarith) (by linarith)
                    · exact leaf03301 x y (by linarith) (by linarith) (by linarith) (by linarith)
                  · by_cases hy0330 : y ≤ (13:ℝ)/32
                    · exact leaf03302 x y (by linarith) (by linarith) (by linarith) (by linarith)
                    · exact leaf03303 x y (by linarith) (by linarith) (by linarith) (by linarith)
                · exact leaf0331 x y (by linarith) (by linarith) (by linarith) (by linarith)
              · by_cases hy033 : y ≤ (7:ℝ)/16
                · exact leaf0332 x y (by linarith) (by linarith) (by linarith) (by linarith)
                · exact leaf0333 x y (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hx1 : x ≤ (1:ℝ)/4
      · by_cases hy1 : y ≤ (3:ℝ)/4
        · exact leaf10 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · exact leaf11 x y (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hy1 : y ≤ (3:ℝ)/4
        · exact leaf12 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · exact leaf13 x y (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hyroot : y ≤ (1:ℝ)/2
    · by_cases hx2 : x ≤ (3:ℝ)/4
      · by_cases hy2 : y ≤ (1:ℝ)/4
        · exact leaf20 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · exact leaf21 x y (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hy2 : y ≤ (1:ℝ)/4
        · exact leaf22 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · exact leaf23 x y (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hx3 : x ≤ (3:ℝ)/4
      · by_cases hy3 : y ≤ (3:ℝ)/4
        · exact leaf30 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · exact leaf31 x y (by linarith) (by linarith) (by linarith) (by linarith)
      · by_cases hy3 : y ≤ (3:ℝ)/4
        · exact leaf32 x y (by linarith) (by linarith) (by linarith) (by linarith)
        · exact leaf33 x y (by linarith) (by linarith) (by linarith) (by linarith)

theorem hC : ∀ z ∈ Q, |C z.1 z.2| ≤ certA := by
  intro z hz
  exact correction_bound z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2

#check hC
#print axioms hC
end
end PoissonR3
