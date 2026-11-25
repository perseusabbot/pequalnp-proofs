import PlaneChecks0
import PlaneChecks1
import PlaneChecks2
import PlaneChecks3
import PlaneChecks4
import PlaneChecks5
import PlaneChecks6
import PlaneChecks7
import PlaneChecks8
import PlaneChecks9
import PlaneChecks10
import PlaneChecks11
import PlaneChecks12

namespace Checkpoint133.Plane
open Data

theorem allChecked (i : ℕ) (hi : i<4877) : Verified lookup i := by
  by_cases h0 : i<64
  · exact inBlock check0 (by omega) h0
  by_cases h1 : i<128
  · exact inBlock check1 (by omega) h1
  by_cases h2 : i<192
  · exact inBlock check2 (by omega) h2
  by_cases h3 : i<256
  · exact inBlock check3 (by omega) h3
  by_cases h4 : i<320
  · exact inBlock check4 (by omega) h4
  by_cases h5 : i<384
  · exact inBlock check5 (by omega) h5
  by_cases h6 : i<448
  · exact inBlock check6 (by omega) h6
  by_cases h7 : i<512
  · exact inBlock check7 (by omega) h7
  by_cases h8 : i<576
  · exact inBlock check8 (by omega) h8
  by_cases h9 : i<640
  · exact inBlock check9 (by omega) h9
  by_cases h10 : i<704
  · exact inBlock check10 (by omega) h10
  by_cases h11 : i<768
  · exact inBlock check11 (by omega) h11
  by_cases h12 : i<832
  · exact inBlock check12 (by omega) h12
  by_cases h13 : i<896
  · exact inBlock check13 (by omega) h13
  by_cases h14 : i<960
  · exact inBlock check14 (by omega) h14
  by_cases h15 : i<1024
  · exact inBlock check15 (by omega) h15
  by_cases h16 : i<1088
  · exact inBlock check16 (by omega) h16
  by_cases h17 : i<1152
  · exact inBlock check17 (by omega) h17
  by_cases h18 : i<1216
  · exact inBlock check18 (by omega) h18
  by_cases h19 : i<1280
  · exact inBlock check19 (by omega) h19
  by_cases h20 : i<1344
  · exact inBlock check20 (by omega) h20
  by_cases h21 : i<1408
  · exact inBlock check21 (by omega) h21
  by_cases h22 : i<1472
  · exact inBlock check22 (by omega) h22
  by_cases h23 : i<1536
  · exact inBlock check23 (by omega) h23
  by_cases h24 : i<1600
  · exact inBlock check24 (by omega) h24
  by_cases h25 : i<1664
  · exact inBlock check25 (by omega) h25
  by_cases h26 : i<1728
  · exact inBlock check26 (by omega) h26
  by_cases h27 : i<1792
  · exact inBlock check27 (by omega) h27
  by_cases h28 : i<1856
  · exact inBlock check28 (by omega) h28
  by_cases h29 : i<1920
  · exact inBlock check29 (by omega) h29
  by_cases h30 : i<1984
  · exact inBlock check30 (by omega) h30
  by_cases h31 : i<2048
  · exact inBlock check31 (by omega) h31
  by_cases h32 : i<2112
  · exact inBlock check32 (by omega) h32
  by_cases h33 : i<2176
  · exact inBlock check33 (by omega) h33
  by_cases h34 : i<2240
  · exact inBlock check34 (by omega) h34
  by_cases h35 : i<2304
  · exact inBlock check35 (by omega) h35
  by_cases h36 : i<2368
  · exact inBlock check36 (by omega) h36
  by_cases h37 : i<2432
  · exact inBlock check37 (by omega) h37
  by_cases h38 : i<2496
  · exact inBlock check38 (by omega) h38
  by_cases h39 : i<2560
  · exact inBlock check39 (by omega) h39
  by_cases h40 : i<2624
  · exact inBlock check40 (by omega) h40
  by_cases h41 : i<2688
  · exact inBlock check41 (by omega) h41
  by_cases h42 : i<2752
  · exact inBlock check42 (by omega) h42
  by_cases h43 : i<2816
  · exact inBlock check43 (by omega) h43
  by_cases h44 : i<2880
  · exact inBlock check44 (by omega) h44
  by_cases h45 : i<2944
  · exact inBlock check45 (by omega) h45
  by_cases h46 : i<3008
  · exact inBlock check46 (by omega) h46
  by_cases h47 : i<3072
  · exact inBlock check47 (by omega) h47
  by_cases h48 : i<3136
  · exact inBlock check48 (by omega) h48
  by_cases h49 : i<3200
  · exact inBlock check49 (by omega) h49
  by_cases h50 : i<3264
  · exact inBlock check50 (by omega) h50
  by_cases h51 : i<3328
  · exact inBlock check51 (by omega) h51
  by_cases h52 : i<3392
  · exact inBlock check52 (by omega) h52
  by_cases h53 : i<3456
  · exact inBlock check53 (by omega) h53
  by_cases h54 : i<3520
  · exact inBlock check54 (by omega) h54
  by_cases h55 : i<3584
  · exact inBlock check55 (by omega) h55
  by_cases h56 : i<3648
  · exact inBlock check56 (by omega) h56
  by_cases h57 : i<3712
  · exact inBlock check57 (by omega) h57
  by_cases h58 : i<3776
  · exact inBlock check58 (by omega) h58
  by_cases h59 : i<3840
  · exact inBlock check59 (by omega) h59
  by_cases h60 : i<3904
  · exact inBlock check60 (by omega) h60
  by_cases h61 : i<3968
  · exact inBlock check61 (by omega) h61
  by_cases h62 : i<4032
  · exact inBlock check62 (by omega) h62
  by_cases h63 : i<4096
  · exact inBlock check63 (by omega) h63
  by_cases h64 : i<4160
  · exact inBlock check64 (by omega) h64
  by_cases h65 : i<4224
  · exact inBlock check65 (by omega) h65
  by_cases h66 : i<4288
  · exact inBlock check66 (by omega) h66
  by_cases h67 : i<4352
  · exact inBlock check67 (by omega) h67
  by_cases h68 : i<4416
  · exact inBlock check68 (by omega) h68
  by_cases h69 : i<4480
  · exact inBlock check69 (by omega) h69
  by_cases h70 : i<4544
  · exact inBlock check70 (by omega) h70
  by_cases h71 : i<4608
  · exact inBlock check71 (by omega) h71
  by_cases h72 : i<4672
  · exact inBlock check72 (by omega) h72
  by_cases h73 : i<4736
  · exact inBlock check73 (by omega) h73
  by_cases h74 : i<4800
  · exact inBlock check74 (by omega) h74
  by_cases h75 : i<4864
  · exact inBlock check75 (by omega) h75
  exact inBlock check76 (by omega) hi

theorem twoOrbits (b d : Box) (hb : Good b) (hd : Good d) : ¬ PairCovers b d := by
  have no := fromTable lookup 4876 (fun j h => allChecked j (by omega))
  have left : (lookup 4876).l=free := by decide +kernel
  have right : (lookup 4876).r=free := by decide +kernel
  rw [left,right] at no
  exact no b d hb hd (freeFits b) (freeFits d)

#print axioms twoOrbits
end Checkpoint133.Plane
