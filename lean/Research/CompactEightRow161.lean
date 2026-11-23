import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block161_0 : checkBlock (R ∪ U) code 161 options161 0 16=true := by decide +kernel
private theorem block161_1 : checkBlock (R ∪ U) code 161 options161 16 16=true := by decide +kernel
private theorem block161_2 : checkBlock (R ∪ U) code 161 options161 32 16=true := by decide +kernel
private theorem block161_3 : checkBlock (R ∪ U) code 161 options161 48 16=true := by decide +kernel
private theorem block161_4 : checkBlock (R ∪ U) code 161 options161 64 16=true := by decide +kernel
private theorem block161_5 : checkBlock (R ∪ U) code 161 options161 80 16=true := by decide +kernel
private theorem block161_6 : checkBlock (R ∪ U) code 161 options161 96 16=true := by decide +kernel
private theorem block161_7 : checkBlock (R ∪ U) code 161 options161 112 16=true := by decide +kernel
private theorem block161_8 : checkBlock (R ∪ U) code 161 options161 128 16=true := by decide +kernel
private theorem block161_9 : checkBlock (R ∪ U) code 161 options161 144 16=true := by decide +kernel
private theorem block161_10 : checkBlock (R ∪ U) code 161 options161 160 16=true := by decide +kernel
private theorem block161_11 : checkBlock (R ∪ U) code 161 options161 176 16=true := by decide +kernel
private theorem block161_12 : checkBlock (R ∪ U) code 161 options161 192 16=true := by decide +kernel
private theorem block161_13 : checkBlock (R ∪ U) code 161 options161 208 16=true := by decide +kernel
private theorem block161_14 : checkBlock (R ∪ U) code 161 options161 224 16=true := by decide +kernel
private theorem block161_15 : checkBlock (R ∪ U) code 161 options161 240 16=true := by decide +kernel
private theorem block161_16 : checkBlock (R ∪ U) code 161 options161 256 16=true := by decide +kernel
private theorem block161_17 : checkBlock (R ∪ U) code 161 options161 272 16=true := by decide +kernel
private theorem block161_18 : checkBlock (R ∪ U) code 161 options161 288 16=true := by decide +kernel
private theorem block161_19 : checkBlock (R ∪ U) code 161 options161 304 16=true := by decide +kernel
private theorem block161_20 : checkBlock (R ∪ U) code 161 options161 320 16=true := by decide +kernel
private theorem block161_21 : checkBlock (R ∪ U) code 161 options161 336 16=true := by decide +kernel
private theorem block161_22 : checkBlock (R ∪ U) code 161 options161 352 16=true := by decide +kernel
private theorem block161_23 : checkBlock (R ∪ U) code 161 options161 368 16=true := by decide +kernel
private theorem block161_24 : checkBlock (R ∪ U) code 161 options161 384 16=true := by decide +kernel
private theorem block161_25 : checkBlock (R ∪ U) code 161 options161 400 16=true := by decide +kernel
private theorem block161_26 : checkBlock (R ∪ U) code 161 options161 416 16=true := by decide +kernel
private theorem block161_27 : checkBlock (R ∪ U) code 161 options161 432 16=true := by decide +kernel
private theorem block161_28 : checkBlock (R ∪ U) code 161 options161 448 16=true := by decide +kernel
private theorem block161_29 : checkBlock (R ∪ U) code 161 options161 464 16=true := by decide +kernel
private theorem block161_30 : checkBlock (R ∪ U) code 161 options161 480 16=true := by decide +kernel
private theorem block161_31 : checkBlock (R ∪ U) code 161 options161 496 16=true := by decide +kernel
theorem check161 : checkRow (R ∪ U) code 161 options161=true := by
  apply combine (R ∪ U) code 161 options161 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block161_0
  · exact block161_1
  · exact block161_2
  · exact block161_3
  · exact block161_4
  · exact block161_5
  · exact block161_6
  · exact block161_7
  · exact block161_8
  · exact block161_9
  · exact block161_10
  · exact block161_11
  · exact block161_12
  · exact block161_13
  · exact block161_14
  · exact block161_15
  · exact block161_16
  · exact block161_17
  · exact block161_18
  · exact block161_19
  · exact block161_20
  · exact block161_21
  · exact block161_22
  · exact block161_23
  · exact block161_24
  · exact block161_25
  · exact block161_26
  · exact block161_27
  · exact block161_28
  · exact block161_29
  · exact block161_30
  · exact block161_31

end PlaneResearch.CompactEight
