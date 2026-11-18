import OutputChecks.B0
import OutputChecks.B1
import OutputChecks.B2
import OutputChecks.B3
import OutputChecks.B4
import OutputChecks.B5
import OutputChecks.B6
import OutputChecks.B7
import OutputChecks.B8
import OutputChecks.B9
import OutputChecks.B10
import OutputChecks.B11
import OutputChecks.B12
import OutputChecks.B13
import OutputChecks.B14
import OutputChecks.B15
import OutputChecks.B16
import OutputChecks.B17
import OutputChecks.B18
import OutputChecks.B19
import OutputChecks.B20
import OutputChecks.B21
import OutputChecks.B22
import OutputChecks.B23
import OutputChecks.B24
import OutputChecks.B25
import OutputChecks.B26
import OutputChecks.B27
import OutputChecks.B28
import OutputChecks.B29
import OutputChecks.B30
import OutputChecks.B31
import OutputChecks.B32
import OutputChecks.B33
import OutputChecks.B34
import OutputChecks.B35
import OutputChecks.B36
import OutputChecks.B37
import OutputChecks.B38
import OutputChecks.B39
import OutputChecks.B40
import OutputChecks.B41
import OutputChecks.B42
import OutputChecks.B43
import OutputChecks.B44
import OutputChecks.B45
import OutputChecks.B46
import OutputChecks.B47
import OutputChecks.B48
import OutputChecks.B49
import OutputChecks.B50
import OutputChecks.B51
import OutputChecks.B52
import OutputChecks.B53
import OutputChecks.B54
import OutputChecks.B55
import OutputChecks.B56
import OutputChecks.B57
import OutputChecks.B58
import OutputChecks.B59
import OutputChecks.B60
import OutputChecks.B61
import OutputChecks.B62
import OutputChecks.B63
import OutputChecks.B64
import OutputChecks.B65
import OutputChecks.B66
import OutputChecks.B67
import OutputChecks.B68
import OutputChecks.B69
import OutputChecks.B70
import OutputChecks.B71
import OutputChecks.B72
import OutputChecks.B73
import OutputChecks.B74
import OutputChecks.B75
import OutputChecks.B76
import OutputChecks.B77
import OutputChecks.B78
import OutputChecks.B79
import OutputChecks.B80
import OutputChecks.B81
import OutputChecks.B82
import OutputChecks.B83
import OutputChecks.B84
import OutputChecks.B85
import OutputChecks.B86
import OutputChecks.B87
import OutputChecks.B88
import OutputChecks.B89
import OutputChecks.B90
import OutputChecks.B91
import OutputChecks.B92
import OutputChecks.B93
import OutputChecks.B94
import OutputChecks.B95
import OutputChecks.B96
import OutputChecks.B97
import OutputChecks.B98
import OutputChecks.B99
import OutputChecks.B100
import OutputChecks.B101
import OutputChecks.B102
import OutputChecks.B103
import OutputChecks.B104
import OutputChecks.B105
import OutputChecks.B106
import OutputChecks.B107
import OutputChecks.B108
import OutputChecks.B109
import OutputChecks.B110
import OutputChecks.B111
import OutputChecks.B112
import OutputChecks.B113
import OutputChecks.B114
import OutputChecks.B115
import OutputChecks.B116
import OutputChecks.B117
import OutputChecks.B118
import OutputChecks.B119
import OutputChecks.B120
import OutputChecks.B121
import OutputChecks.B122
import OutputChecks.B123
import OutputChecks.B124
import OutputChecks.B125
import OutputChecks.B126
import OutputChecks.B127
import OutputChecks.B128
import OutputChecks.B129
import OutputChecks.B130
import OutputChecks.B131
import OutputChecks.B132
import OutputChecks.B133
import OutputChecks.B134
import OutputChecks.B135
import OutputChecks.B136
import OutputChecks.B137
import OutputChecks.B138
import OutputChecks.B139
import OutputChecks.B140
import OutputChecks.B141
import OutputChecks.B142
import OutputChecks.B143
import OutputChecks.B144
import OutputChecks.B145
import OutputChecks.B146
import OutputChecks.B147
import OutputChecks.B148
import OutputChecks.B149
import OutputChecks.B150
import OutputChecks.B151
import OutputChecks.B152
import OutputChecks.B153
import OutputChecks.B154
import OutputChecks.B155
import OutputChecks.B156
import OutputChecks.B157
import OutputChecks.B158
import OutputChecks.B159
import OutputChecks.B160
import OutputChecks.B161
import OutputChecks.B162
import OutputChecks.B163
import OutputChecks.B164
import OutputChecks.B165
import OutputChecks.B166
import OutputChecks.B167
import OutputChecks.B168
import OutputChecks.B169
import OutputChecks.B170
import OutputChecks.B171
import OutputChecks.B172
import OutputChecks.B173
import OutputChecks.B174
import OutputChecks.B175
import OutputChecks.B176
import OutputChecks.B177
import OutputChecks.B178
import OutputChecks.B179
import OutputChecks.B180
import OutputChecks.B181
import OutputChecks.B182
import OutputChecks.B183
import OutputChecks.B184
import OutputChecks.B185
import OutputChecks.B186
import OutputChecks.B187
import OutputChecks.B188
import OutputChecks.B189
import OutputChecks.B190
import OutputChecks.B191
import OutputChecks.B192
import OutputChecks.B193
import OutputChecks.B194
import OutputChecks.B195
import OutputChecks.B196

namespace PythiaCert.Output
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all_blocks_checked : ∀ k, k < 197 → centerBlock k = true := by
  intro k hk
  interval_cases k
  · exact block0_checked
  · exact block1_checked
  · exact block2_checked
  · exact block3_checked
  · exact block4_checked
  · exact block5_checked
  · exact block6_checked
  · exact block7_checked
  · exact block8_checked
  · exact block9_checked
  · exact block10_checked
  · exact block11_checked
  · exact block12_checked
  · exact block13_checked
  · exact block14_checked
  · exact block15_checked
  · exact block16_checked
  · exact block17_checked
  · exact block18_checked
  · exact block19_checked
  · exact block20_checked
  · exact block21_checked
  · exact block22_checked
  · exact block23_checked
  · exact block24_checked
  · exact block25_checked
  · exact block26_checked
  · exact block27_checked
  · exact block28_checked
  · exact block29_checked
  · exact block30_checked
  · exact block31_checked
  · exact block32_checked
  · exact block33_checked
  · exact block34_checked
  · exact block35_checked
  · exact block36_checked
  · exact block37_checked
  · exact block38_checked
  · exact block39_checked
  · exact block40_checked
  · exact block41_checked
  · exact block42_checked
  · exact block43_checked
  · exact block44_checked
  · exact block45_checked
  · exact block46_checked
  · exact block47_checked
  · exact block48_checked
  · exact block49_checked
  · exact block50_checked
  · exact block51_checked
  · exact block52_checked
  · exact block53_checked
  · exact block54_checked
  · exact block55_checked
  · exact block56_checked
  · exact block57_checked
  · exact block58_checked
  · exact block59_checked
  · exact block60_checked
  · exact block61_checked
  · exact block62_checked
  · exact block63_checked
  · exact block64_checked
  · exact block65_checked
  · exact block66_checked
  · exact block67_checked
  · exact block68_checked
  · exact block69_checked
  · exact block70_checked
  · exact block71_checked
  · exact block72_checked
  · exact block73_checked
  · exact block74_checked
  · exact block75_checked
  · exact block76_checked
  · exact block77_checked
  · exact block78_checked
  · exact block79_checked
  · exact block80_checked
  · exact block81_checked
  · exact block82_checked
  · exact block83_checked
  · exact block84_checked
  · exact block85_checked
  · exact block86_checked
  · exact block87_checked
  · exact block88_checked
  · exact block89_checked
  · exact block90_checked
  · exact block91_checked
  · exact block92_checked
  · exact block93_checked
  · exact block94_checked
  · exact block95_checked
  · exact block96_checked
  · exact block97_checked
  · exact block98_checked
  · exact block99_checked
  · exact block100_checked
  · exact block101_checked
  · exact block102_checked
  · exact block103_checked
  · exact block104_checked
  · exact block105_checked
  · exact block106_checked
  · exact block107_checked
  · exact block108_checked
  · exact block109_checked
  · exact block110_checked
  · exact block111_checked
  · exact block112_checked
  · exact block113_checked
  · exact block114_checked
  · exact block115_checked
  · exact block116_checked
  · exact block117_checked
  · exact block118_checked
  · exact block119_checked
  · exact block120_checked
  · exact block121_checked
  · exact block122_checked
  · exact block123_checked
  · exact block124_checked
  · exact block125_checked
  · exact block126_checked
  · exact block127_checked
  · exact block128_checked
  · exact block129_checked
  · exact block130_checked
  · exact block131_checked
  · exact block132_checked
  · exact block133_checked
  · exact block134_checked
  · exact block135_checked
  · exact block136_checked
  · exact block137_checked
  · exact block138_checked
  · exact block139_checked
  · exact block140_checked
  · exact block141_checked
  · exact block142_checked
  · exact block143_checked
  · exact block144_checked
  · exact block145_checked
  · exact block146_checked
  · exact block147_checked
  · exact block148_checked
  · exact block149_checked
  · exact block150_checked
  · exact block151_checked
  · exact block152_checked
  · exact block153_checked
  · exact block154_checked
  · exact block155_checked
  · exact block156_checked
  · exact block157_checked
  · exact block158_checked
  · exact block159_checked
  · exact block160_checked
  · exact block161_checked
  · exact block162_checked
  · exact block163_checked
  · exact block164_checked
  · exact block165_checked
  · exact block166_checked
  · exact block167_checked
  · exact block168_checked
  · exact block169_checked
  · exact block170_checked
  · exact block171_checked
  · exact block172_checked
  · exact block173_checked
  · exact block174_checked
  · exact block175_checked
  · exact block176_checked
  · exact block177_checked
  · exact block178_checked
  · exact block179_checked
  · exact block180_checked
  · exact block181_checked
  · exact block182_checked
  · exact block183_checked
  · exact block184_checked
  · exact block185_checked
  · exact block186_checked
  · exact block187_checked
  · exact block188_checked
  · exact block189_checked
  · exact block190_checked
  · exact block191_checked
  · exact block192_checked
  · exact block193_checked
  · exact block194_checked
  · exact block195_checked
  · exact block196_checked
#print axioms all_blocks_checked
end PythiaCert.Output
