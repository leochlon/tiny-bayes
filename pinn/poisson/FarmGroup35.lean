import RawShard2240
import RawShard2241
import RawShard2242
import RawShard2243
import RawShard2244
import RawShard2245
import RawShard2246
import RawShard2247
import RawShard2248
import RawShard2249
import RawShard2250
import RawShard2251
import RawShard2252
import RawShard2253
import RawShard2254
import RawShard2255
import RawShard2256
import RawShard2257
import RawShard2258
import RawShard2259
import RawShard2260
import RawShard2261
import RawShard2262
import RawShard2263
import RawShard2264
import RawShard2265
import RawShard2266
import RawShard2267
import RawShard2268
import RawShard2269
import RawShard2270
import RawShard2271
import RawShard2272
import RawShard2273
import RawShard2274
import RawShard2275
import RawShard2276
import RawShard2277
import RawShard2278
import RawShard2279
import RawShard2280
import RawShard2281
import RawShard2282
import RawShard2283
import RawShard2284
import RawShard2285
import RawShard2286
import RawShard2287
import RawShard2288
import RawShard2289
import RawShard2290
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
open PinnCert
def FarmGroup35Cells : List Cell := RawShard2240Cells ++ RawShard2241Cells ++ RawShard2242Cells ++ RawShard2243Cells ++ RawShard2244Cells ++ RawShard2245Cells ++ RawShard2246Cells ++ RawShard2247Cells ++ RawShard2248Cells ++ RawShard2249Cells ++ RawShard2250Cells ++ RawShard2251Cells ++ RawShard2252Cells ++ RawShard2253Cells ++ RawShard2254Cells ++ RawShard2255Cells ++ RawShard2256Cells ++ RawShard2257Cells ++ RawShard2258Cells ++ RawShard2259Cells ++ RawShard2260Cells ++ RawShard2261Cells ++ RawShard2262Cells ++ RawShard2263Cells ++ RawShard2264Cells ++ RawShard2265Cells ++ RawShard2266Cells ++ RawShard2267Cells ++ RawShard2268Cells ++ RawShard2269Cells ++ RawShard2270Cells ++ RawShard2271Cells ++ RawShard2272Cells ++ RawShard2273Cells ++ RawShard2274Cells ++ RawShard2275Cells ++ RawShard2276Cells ++ RawShard2277Cells ++ RawShard2278Cells ++ RawShard2279Cells ++ RawShard2280Cells ++ RawShard2281Cells ++ RawShard2282Cells ++ RawShard2283Cells ++ RawShard2284Cells ++ RawShard2285Cells ++ RawShard2286Cells ++ RawShard2287Cells ++ RawShard2288Cells ++ RawShard2289Cells ++ RawShard2290Cells
theorem FarmGroup35Valid : ValidCells FarmGroup35Cells := by
  unfold FarmGroup35Cells
  simp only [List.append_assoc]
  exact (valid_append RawShard2240Valid (valid_append RawShard2241Valid (valid_append RawShard2242Valid (valid_append RawShard2243Valid (valid_append RawShard2244Valid (valid_append RawShard2245Valid (valid_append RawShard2246Valid (valid_append RawShard2247Valid (valid_append RawShard2248Valid (valid_append RawShard2249Valid (valid_append RawShard2250Valid (valid_append RawShard2251Valid (valid_append RawShard2252Valid (valid_append RawShard2253Valid (valid_append RawShard2254Valid (valid_append RawShard2255Valid (valid_append RawShard2256Valid (valid_append RawShard2257Valid (valid_append RawShard2258Valid (valid_append RawShard2259Valid (valid_append RawShard2260Valid (valid_append RawShard2261Valid (valid_append RawShard2262Valid (valid_append RawShard2263Valid (valid_append RawShard2264Valid (valid_append RawShard2265Valid (valid_append RawShard2266Valid (valid_append RawShard2267Valid (valid_append RawShard2268Valid (valid_append RawShard2269Valid (valid_append RawShard2270Valid (valid_append RawShard2271Valid (valid_append RawShard2272Valid (valid_append RawShard2273Valid (valid_append RawShard2274Valid (valid_append RawShard2275Valid (valid_append RawShard2276Valid (valid_append RawShard2277Valid (valid_append RawShard2278Valid (valid_append RawShard2279Valid (valid_append RawShard2280Valid (valid_append RawShard2281Valid (valid_append RawShard2282Valid (valid_append RawShard2283Valid (valid_append RawShard2284Valid (valid_append RawShard2285Valid (valid_append RawShard2286Valid (valid_append RawShard2287Valid (valid_append RawShard2288Valid (valid_append RawShard2289Valid RawShard2290Valid))))))))))))))))))))))))))))))))))))))))))))))))))
end PinnCertFarm
