import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block138_0 : checkBlock (R ∪ U) code 138 options138 0 16=true := by decide +kernel
private theorem block138_1 : checkBlock (R ∪ U) code 138 options138 16 16=true := by decide +kernel
private theorem block138_2 : checkBlock (R ∪ U) code 138 options138 32 16=true := by decide +kernel
private theorem block138_3 : checkBlock (R ∪ U) code 138 options138 48 16=true := by decide +kernel
private theorem block138_4 : checkBlock (R ∪ U) code 138 options138 64 16=true := by decide +kernel
private theorem block138_5 : checkBlock (R ∪ U) code 138 options138 80 16=true := by decide +kernel
private theorem block138_6 : checkBlock (R ∪ U) code 138 options138 96 16=true := by decide +kernel
private theorem block138_7 : checkBlock (R ∪ U) code 138 options138 112 16=true := by decide +kernel
private theorem block138_8 : checkBlock (R ∪ U) code 138 options138 128 16=true := by decide +kernel
private theorem block138_9 : checkBlock (R ∪ U) code 138 options138 144 16=true := by decide +kernel
private theorem block138_10 : checkBlock (R ∪ U) code 138 options138 160 16=true := by decide +kernel
private theorem block138_11 : checkBlock (R ∪ U) code 138 options138 176 16=true := by decide +kernel
private theorem block138_12 : checkBlock (R ∪ U) code 138 options138 192 16=true := by decide +kernel
private theorem block138_13 : checkBlock (R ∪ U) code 138 options138 208 16=true := by decide +kernel
private theorem block138_14 : checkBlock (R ∪ U) code 138 options138 224 16=true := by decide +kernel
private theorem block138_15 : checkBlock (R ∪ U) code 138 options138 240 16=true := by decide +kernel
private theorem block138_16 : checkBlock (R ∪ U) code 138 options138 256 16=true := by decide +kernel
private theorem block138_17 : checkBlock (R ∪ U) code 138 options138 272 16=true := by decide +kernel
private theorem block138_18 : checkBlock (R ∪ U) code 138 options138 288 16=true := by decide +kernel
private theorem block138_19 : checkBlock (R ∪ U) code 138 options138 304 16=true := by decide +kernel
private theorem block138_20 : checkBlock (R ∪ U) code 138 options138 320 16=true := by decide +kernel
private theorem block138_21 : checkBlock (R ∪ U) code 138 options138 336 16=true := by decide +kernel
private theorem block138_22 : checkBlock (R ∪ U) code 138 options138 352 16=true := by decide +kernel
private theorem block138_23 : checkBlock (R ∪ U) code 138 options138 368 16=true := by decide +kernel
private theorem block138_24 : checkBlock (R ∪ U) code 138 options138 384 16=true := by decide +kernel
private theorem block138_25 : checkBlock (R ∪ U) code 138 options138 400 16=true := by decide +kernel
private theorem block138_26 : checkBlock (R ∪ U) code 138 options138 416 16=true := by decide +kernel
private theorem block138_27 : checkBlock (R ∪ U) code 138 options138 432 16=true := by decide +kernel
private theorem block138_28 : checkBlock (R ∪ U) code 138 options138 448 16=true := by decide +kernel
private theorem block138_29 : checkBlock (R ∪ U) code 138 options138 464 16=true := by decide +kernel
private theorem block138_30 : checkBlock (R ∪ U) code 138 options138 480 16=true := by decide +kernel
private theorem block138_31 : checkBlock (R ∪ U) code 138 options138 496 16=true := by decide +kernel
theorem check138 : checkRow (R ∪ U) code 138 options138=true := by
  apply combine (R ∪ U) code 138 options138 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block138_0
  · exact block138_1
  · exact block138_2
  · exact block138_3
  · exact block138_4
  · exact block138_5
  · exact block138_6
  · exact block138_7
  · exact block138_8
  · exact block138_9
  · exact block138_10
  · exact block138_11
  · exact block138_12
  · exact block138_13
  · exact block138_14
  · exact block138_15
  · exact block138_16
  · exact block138_17
  · exact block138_18
  · exact block138_19
  · exact block138_20
  · exact block138_21
  · exact block138_22
  · exact block138_23
  · exact block138_24
  · exact block138_25
  · exact block138_26
  · exact block138_27
  · exact block138_28
  · exact block138_29
  · exact block138_30
  · exact block138_31

end PlaneResearch.CompactEight
