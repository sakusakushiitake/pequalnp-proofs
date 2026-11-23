import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block22_0 : checkBlock (R ∪ U) code 22 options22 0 16=true := by decide +kernel
private theorem block22_1 : checkBlock (R ∪ U) code 22 options22 16 16=true := by decide +kernel
private theorem block22_2 : checkBlock (R ∪ U) code 22 options22 32 16=true := by decide +kernel
private theorem block22_3 : checkBlock (R ∪ U) code 22 options22 48 16=true := by decide +kernel
private theorem block22_4 : checkBlock (R ∪ U) code 22 options22 64 16=true := by decide +kernel
private theorem block22_5 : checkBlock (R ∪ U) code 22 options22 80 16=true := by decide +kernel
private theorem block22_6 : checkBlock (R ∪ U) code 22 options22 96 16=true := by decide +kernel
private theorem block22_7 : checkBlock (R ∪ U) code 22 options22 112 16=true := by decide +kernel
private theorem block22_8 : checkBlock (R ∪ U) code 22 options22 128 16=true := by decide +kernel
private theorem block22_9 : checkBlock (R ∪ U) code 22 options22 144 16=true := by decide +kernel
private theorem block22_10 : checkBlock (R ∪ U) code 22 options22 160 16=true := by decide +kernel
private theorem block22_11 : checkBlock (R ∪ U) code 22 options22 176 16=true := by decide +kernel
private theorem block22_12 : checkBlock (R ∪ U) code 22 options22 192 16=true := by decide +kernel
private theorem block22_13 : checkBlock (R ∪ U) code 22 options22 208 16=true := by decide +kernel
private theorem block22_14 : checkBlock (R ∪ U) code 22 options22 224 16=true := by decide +kernel
private theorem block22_15 : checkBlock (R ∪ U) code 22 options22 240 16=true := by decide +kernel
private theorem block22_16 : checkBlock (R ∪ U) code 22 options22 256 16=true := by decide +kernel
private theorem block22_17 : checkBlock (R ∪ U) code 22 options22 272 16=true := by decide +kernel
private theorem block22_18 : checkBlock (R ∪ U) code 22 options22 288 16=true := by decide +kernel
private theorem block22_19 : checkBlock (R ∪ U) code 22 options22 304 16=true := by decide +kernel
private theorem block22_20 : checkBlock (R ∪ U) code 22 options22 320 16=true := by decide +kernel
private theorem block22_21 : checkBlock (R ∪ U) code 22 options22 336 16=true := by decide +kernel
private theorem block22_22 : checkBlock (R ∪ U) code 22 options22 352 16=true := by decide +kernel
private theorem block22_23 : checkBlock (R ∪ U) code 22 options22 368 16=true := by decide +kernel
private theorem block22_24 : checkBlock (R ∪ U) code 22 options22 384 16=true := by decide +kernel
private theorem block22_25 : checkBlock (R ∪ U) code 22 options22 400 16=true := by decide +kernel
private theorem block22_26 : checkBlock (R ∪ U) code 22 options22 416 16=true := by decide +kernel
private theorem block22_27 : checkBlock (R ∪ U) code 22 options22 432 16=true := by decide +kernel
private theorem block22_28 : checkBlock (R ∪ U) code 22 options22 448 16=true := by decide +kernel
private theorem block22_29 : checkBlock (R ∪ U) code 22 options22 464 16=true := by decide +kernel
private theorem block22_30 : checkBlock (R ∪ U) code 22 options22 480 16=true := by decide +kernel
private theorem block22_31 : checkBlock (R ∪ U) code 22 options22 496 16=true := by decide +kernel
theorem check22 : checkRow (R ∪ U) code 22 options22=true := by
  apply combine (R ∪ U) code 22 options22 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block22_0
  · exact block22_1
  · exact block22_2
  · exact block22_3
  · exact block22_4
  · exact block22_5
  · exact block22_6
  · exact block22_7
  · exact block22_8
  · exact block22_9
  · exact block22_10
  · exact block22_11
  · exact block22_12
  · exact block22_13
  · exact block22_14
  · exact block22_15
  · exact block22_16
  · exact block22_17
  · exact block22_18
  · exact block22_19
  · exact block22_20
  · exact block22_21
  · exact block22_22
  · exact block22_23
  · exact block22_24
  · exact block22_25
  · exact block22_26
  · exact block22_27
  · exact block22_28
  · exact block22_29
  · exact block22_30
  · exact block22_31

end PlaneResearch.CompactEight
