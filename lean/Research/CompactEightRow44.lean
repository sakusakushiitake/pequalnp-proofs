import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block44_0 : checkBlock (R ∪ U) code 44 options44 0 16=true := by decide +kernel
private theorem block44_1 : checkBlock (R ∪ U) code 44 options44 16 16=true := by decide +kernel
private theorem block44_2 : checkBlock (R ∪ U) code 44 options44 32 16=true := by decide +kernel
private theorem block44_3 : checkBlock (R ∪ U) code 44 options44 48 16=true := by decide +kernel
private theorem block44_4 : checkBlock (R ∪ U) code 44 options44 64 16=true := by decide +kernel
private theorem block44_5 : checkBlock (R ∪ U) code 44 options44 80 16=true := by decide +kernel
private theorem block44_6 : checkBlock (R ∪ U) code 44 options44 96 16=true := by decide +kernel
private theorem block44_7 : checkBlock (R ∪ U) code 44 options44 112 16=true := by decide +kernel
private theorem block44_8 : checkBlock (R ∪ U) code 44 options44 128 16=true := by decide +kernel
private theorem block44_9 : checkBlock (R ∪ U) code 44 options44 144 16=true := by decide +kernel
private theorem block44_10 : checkBlock (R ∪ U) code 44 options44 160 16=true := by decide +kernel
private theorem block44_11 : checkBlock (R ∪ U) code 44 options44 176 16=true := by decide +kernel
private theorem block44_12 : checkBlock (R ∪ U) code 44 options44 192 16=true := by decide +kernel
private theorem block44_13 : checkBlock (R ∪ U) code 44 options44 208 16=true := by decide +kernel
private theorem block44_14 : checkBlock (R ∪ U) code 44 options44 224 16=true := by decide +kernel
private theorem block44_15 : checkBlock (R ∪ U) code 44 options44 240 16=true := by decide +kernel
private theorem block44_16 : checkBlock (R ∪ U) code 44 options44 256 16=true := by decide +kernel
private theorem block44_17 : checkBlock (R ∪ U) code 44 options44 272 16=true := by decide +kernel
private theorem block44_18 : checkBlock (R ∪ U) code 44 options44 288 16=true := by decide +kernel
private theorem block44_19 : checkBlock (R ∪ U) code 44 options44 304 16=true := by decide +kernel
private theorem block44_20 : checkBlock (R ∪ U) code 44 options44 320 16=true := by decide +kernel
private theorem block44_21 : checkBlock (R ∪ U) code 44 options44 336 16=true := by decide +kernel
private theorem block44_22 : checkBlock (R ∪ U) code 44 options44 352 16=true := by decide +kernel
private theorem block44_23 : checkBlock (R ∪ U) code 44 options44 368 16=true := by decide +kernel
private theorem block44_24 : checkBlock (R ∪ U) code 44 options44 384 16=true := by decide +kernel
private theorem block44_25 : checkBlock (R ∪ U) code 44 options44 400 16=true := by decide +kernel
private theorem block44_26 : checkBlock (R ∪ U) code 44 options44 416 16=true := by decide +kernel
private theorem block44_27 : checkBlock (R ∪ U) code 44 options44 432 16=true := by decide +kernel
private theorem block44_28 : checkBlock (R ∪ U) code 44 options44 448 16=true := by decide +kernel
private theorem block44_29 : checkBlock (R ∪ U) code 44 options44 464 16=true := by decide +kernel
private theorem block44_30 : checkBlock (R ∪ U) code 44 options44 480 16=true := by decide +kernel
private theorem block44_31 : checkBlock (R ∪ U) code 44 options44 496 16=true := by decide +kernel
theorem check44 : checkRow (R ∪ U) code 44 options44=true := by
  apply combine (R ∪ U) code 44 options44 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block44_0
  · exact block44_1
  · exact block44_2
  · exact block44_3
  · exact block44_4
  · exact block44_5
  · exact block44_6
  · exact block44_7
  · exact block44_8
  · exact block44_9
  · exact block44_10
  · exact block44_11
  · exact block44_12
  · exact block44_13
  · exact block44_14
  · exact block44_15
  · exact block44_16
  · exact block44_17
  · exact block44_18
  · exact block44_19
  · exact block44_20
  · exact block44_21
  · exact block44_22
  · exact block44_23
  · exact block44_24
  · exact block44_25
  · exact block44_26
  · exact block44_27
  · exact block44_28
  · exact block44_29
  · exact block44_30
  · exact block44_31

end PlaneResearch.CompactEight
