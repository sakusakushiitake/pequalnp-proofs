import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block208_0 : checkBlock (R ∪ U) code 208 options208 0 16=true := by decide +kernel
private theorem block208_1 : checkBlock (R ∪ U) code 208 options208 16 16=true := by decide +kernel
private theorem block208_2 : checkBlock (R ∪ U) code 208 options208 32 16=true := by decide +kernel
private theorem block208_3 : checkBlock (R ∪ U) code 208 options208 48 16=true := by decide +kernel
private theorem block208_4 : checkBlock (R ∪ U) code 208 options208 64 16=true := by decide +kernel
private theorem block208_5 : checkBlock (R ∪ U) code 208 options208 80 16=true := by decide +kernel
private theorem block208_6 : checkBlock (R ∪ U) code 208 options208 96 16=true := by decide +kernel
private theorem block208_7 : checkBlock (R ∪ U) code 208 options208 112 16=true := by decide +kernel
private theorem block208_8 : checkBlock (R ∪ U) code 208 options208 128 16=true := by decide +kernel
private theorem block208_9 : checkBlock (R ∪ U) code 208 options208 144 16=true := by decide +kernel
private theorem block208_10 : checkBlock (R ∪ U) code 208 options208 160 16=true := by decide +kernel
private theorem block208_11 : checkBlock (R ∪ U) code 208 options208 176 16=true := by decide +kernel
private theorem block208_12 : checkBlock (R ∪ U) code 208 options208 192 16=true := by decide +kernel
private theorem block208_13 : checkBlock (R ∪ U) code 208 options208 208 16=true := by decide +kernel
private theorem block208_14 : checkBlock (R ∪ U) code 208 options208 224 16=true := by decide +kernel
private theorem block208_15 : checkBlock (R ∪ U) code 208 options208 240 16=true := by decide +kernel
private theorem block208_16 : checkBlock (R ∪ U) code 208 options208 256 16=true := by decide +kernel
private theorem block208_17 : checkBlock (R ∪ U) code 208 options208 272 16=true := by decide +kernel
private theorem block208_18 : checkBlock (R ∪ U) code 208 options208 288 16=true := by decide +kernel
private theorem block208_19 : checkBlock (R ∪ U) code 208 options208 304 16=true := by decide +kernel
private theorem block208_20 : checkBlock (R ∪ U) code 208 options208 320 16=true := by decide +kernel
private theorem block208_21 : checkBlock (R ∪ U) code 208 options208 336 16=true := by decide +kernel
private theorem block208_22 : checkBlock (R ∪ U) code 208 options208 352 16=true := by decide +kernel
private theorem block208_23 : checkBlock (R ∪ U) code 208 options208 368 16=true := by decide +kernel
private theorem block208_24 : checkBlock (R ∪ U) code 208 options208 384 16=true := by decide +kernel
private theorem block208_25 : checkBlock (R ∪ U) code 208 options208 400 16=true := by decide +kernel
private theorem block208_26 : checkBlock (R ∪ U) code 208 options208 416 16=true := by decide +kernel
private theorem block208_27 : checkBlock (R ∪ U) code 208 options208 432 16=true := by decide +kernel
private theorem block208_28 : checkBlock (R ∪ U) code 208 options208 448 16=true := by decide +kernel
private theorem block208_29 : checkBlock (R ∪ U) code 208 options208 464 16=true := by decide +kernel
private theorem block208_30 : checkBlock (R ∪ U) code 208 options208 480 16=true := by decide +kernel
private theorem block208_31 : checkBlock (R ∪ U) code 208 options208 496 16=true := by decide +kernel
theorem check208 : checkRow (R ∪ U) code 208 options208=true := by
  apply combine (R ∪ U) code 208 options208 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block208_0
  · exact block208_1
  · exact block208_2
  · exact block208_3
  · exact block208_4
  · exact block208_5
  · exact block208_6
  · exact block208_7
  · exact block208_8
  · exact block208_9
  · exact block208_10
  · exact block208_11
  · exact block208_12
  · exact block208_13
  · exact block208_14
  · exact block208_15
  · exact block208_16
  · exact block208_17
  · exact block208_18
  · exact block208_19
  · exact block208_20
  · exact block208_21
  · exact block208_22
  · exact block208_23
  · exact block208_24
  · exact block208_25
  · exact block208_26
  · exact block208_27
  · exact block208_28
  · exact block208_29
  · exact block208_30
  · exact block208_31

end PlaneResearch.CompactEight
