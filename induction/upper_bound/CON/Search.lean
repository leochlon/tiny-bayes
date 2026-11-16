import Mathlib
import CON.Groups
import CON.S.C0
import CON.S.C1
import CON.S.C2
import CON.S.C3
import CON.S.C4
import CON.S.C5
import CON.S.C6
import CON.S.C7
import CON.S.C8
import CON.S.C9
import CON.S.C10
import CON.S.C11
import CON.S.C12
import CON.S.C13
import CON.S.C14
import CON.S.C15
import CON.S.C16
import CON.S.C17
import CON.S.C18
import CON.S.C19
import CON.S.C20
import CON.S.C21
import CON.S.C22
import CON.S.C23
import CON.S.C24
import CON.S.C25
import CON.S.C26
import CON.S.C27
import CON.S.C28
import CON.S.C29
import CON.S.C30
import CON.S.C31
import CON.S.C32
import CON.S.C33
import CON.S.C34
import CON.S.C35
import CON.S.C36
import CON.S.C37
import CON.S.C38
import CON.S.C39
import CON.S.C40
import CON.S.C41

/-! The exhaustive search stays within the capacity `caps3[c]` for every group (kernel computations in
`CON.S.*`, one module per four groups). -/

namespace CON

theorem searchOK (c : ℕ) (hc : c < 167) :
    mx (freeMasks.getD c 0) (groups.getD c []).length [] ≤ caps3.getD c 0 := by
  have h : classOK c = true := by
    by_cases h0 : c < 4
    · exact S.ok0 c h0 (Nat.zero_le _)
    by_cases h1 : c < 8
    · exact S.ok1 c h1 (not_lt.mp h0)
    by_cases h2 : c < 12
    · exact S.ok2 c h2 (not_lt.mp h1)
    by_cases h3 : c < 16
    · exact S.ok3 c h3 (not_lt.mp h2)
    by_cases h4 : c < 20
    · exact S.ok4 c h4 (not_lt.mp h3)
    by_cases h5 : c < 24
    · exact S.ok5 c h5 (not_lt.mp h4)
    by_cases h6 : c < 28
    · exact S.ok6 c h6 (not_lt.mp h5)
    by_cases h7 : c < 32
    · exact S.ok7 c h7 (not_lt.mp h6)
    by_cases h8 : c < 36
    · exact S.ok8 c h8 (not_lt.mp h7)
    by_cases h9 : c < 40
    · exact S.ok9 c h9 (not_lt.mp h8)
    by_cases h10 : c < 44
    · exact S.ok10 c h10 (not_lt.mp h9)
    by_cases h11 : c < 48
    · exact S.ok11 c h11 (not_lt.mp h10)
    by_cases h12 : c < 52
    · exact S.ok12 c h12 (not_lt.mp h11)
    by_cases h13 : c < 56
    · exact S.ok13 c h13 (not_lt.mp h12)
    by_cases h14 : c < 60
    · exact S.ok14 c h14 (not_lt.mp h13)
    by_cases h15 : c < 64
    · exact S.ok15 c h15 (not_lt.mp h14)
    by_cases h16 : c < 68
    · exact S.ok16 c h16 (not_lt.mp h15)
    by_cases h17 : c < 72
    · exact S.ok17 c h17 (not_lt.mp h16)
    by_cases h18 : c < 76
    · exact S.ok18 c h18 (not_lt.mp h17)
    by_cases h19 : c < 80
    · exact S.ok19 c h19 (not_lt.mp h18)
    by_cases h20 : c < 84
    · exact S.ok20 c h20 (not_lt.mp h19)
    by_cases h21 : c < 88
    · exact S.ok21 c h21 (not_lt.mp h20)
    by_cases h22 : c < 92
    · exact S.ok22 c h22 (not_lt.mp h21)
    by_cases h23 : c < 96
    · exact S.ok23 c h23 (not_lt.mp h22)
    by_cases h24 : c < 100
    · exact S.ok24 c h24 (not_lt.mp h23)
    by_cases h25 : c < 104
    · exact S.ok25 c h25 (not_lt.mp h24)
    by_cases h26 : c < 108
    · exact S.ok26 c h26 (not_lt.mp h25)
    by_cases h27 : c < 112
    · exact S.ok27 c h27 (not_lt.mp h26)
    by_cases h28 : c < 116
    · exact S.ok28 c h28 (not_lt.mp h27)
    by_cases h29 : c < 120
    · exact S.ok29 c h29 (not_lt.mp h28)
    by_cases h30 : c < 124
    · exact S.ok30 c h30 (not_lt.mp h29)
    by_cases h31 : c < 128
    · exact S.ok31 c h31 (not_lt.mp h30)
    by_cases h32 : c < 132
    · exact S.ok32 c h32 (not_lt.mp h31)
    by_cases h33 : c < 136
    · exact S.ok33 c h33 (not_lt.mp h32)
    by_cases h34 : c < 140
    · exact S.ok34 c h34 (not_lt.mp h33)
    by_cases h35 : c < 144
    · exact S.ok35 c h35 (not_lt.mp h34)
    by_cases h36 : c < 148
    · exact S.ok36 c h36 (not_lt.mp h35)
    by_cases h37 : c < 152
    · exact S.ok37 c h37 (not_lt.mp h36)
    by_cases h38 : c < 156
    · exact S.ok38 c h38 (not_lt.mp h37)
    by_cases h39 : c < 160
    · exact S.ok39 c h39 (not_lt.mp h38)
    by_cases h40 : c < 164
    · exact S.ok40 c h40 (not_lt.mp h39)
    exact S.ok41 c hc (not_lt.mp h40)
  exact of_decide_eq_true h

end CON
