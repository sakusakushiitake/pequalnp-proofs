import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block25_0 : checkBlock (R ∪ U) code 25 options25 0 16=true := by decide +kernel
private theorem block25_1 : checkBlock (R ∪ U) code 25 options25 16 16=true := by decide +kernel
private theorem block25_2 : checkBlock (R ∪ U) code 25 options25 32 16=true := by decide +kernel
private theorem block25_3 : checkBlock (R ∪ U) code 25 options25 48 16=true := by decide +kernel
private theorem block25_4 : checkBlock (R ∪ U) code 25 options25 64 16=true := by decide +kernel
private theorem block25_5 : checkBlock (R ∪ U) code 25 options25 80 16=true := by decide +kernel
private theorem block25_6 : checkBlock (R ∪ U) code 25 options25 96 16=true := by decide +kernel
private theorem block25_7 : checkBlock (R ∪ U) code 25 options25 112 16=true := by decide +kernel
private theorem block25_8 : checkBlock (R ∪ U) code 25 options25 128 16=true := by decide +kernel
private theorem block25_9 : checkBlock (R ∪ U) code 25 options25 144 16=true := by decide +kernel
private theorem block25_10 : checkBlock (R ∪ U) code 25 options25 160 16=true := by decide +kernel
private theorem block25_11 : checkBlock (R ∪ U) code 25 options25 176 16=true := by decide +kernel
private theorem block25_12 : checkBlock (R ∪ U) code 25 options25 192 16=true := by decide +kernel
private theorem block25_13 : checkBlock (R ∪ U) code 25 options25 208 16=true := by decide +kernel
private theorem block25_14 : checkBlock (R ∪ U) code 25 options25 224 16=true := by decide +kernel
private theorem block25_15 : checkBlock (R ∪ U) code 25 options25 240 16=true := by decide +kernel
private theorem block25_16 : checkBlock (R ∪ U) code 25 options25 256 16=true := by decide +kernel
private theorem block25_17 : checkBlock (R ∪ U) code 25 options25 272 16=true := by decide +kernel
private theorem block25_18 : checkBlock (R ∪ U) code 25 options25 288 16=true := by decide +kernel
private theorem block25_19 : checkBlock (R ∪ U) code 25 options25 304 16=true := by decide +kernel
private theorem block25_20 : checkBlock (R ∪ U) code 25 options25 320 16=true := by decide +kernel
private theorem block25_21 : checkBlock (R ∪ U) code 25 options25 336 16=true := by decide +kernel
private theorem block25_22 : checkBlock (R ∪ U) code 25 options25 352 16=true := by decide +kernel
private theorem block25_23 : checkBlock (R ∪ U) code 25 options25 368 16=true := by decide +kernel
private theorem block25_24 : checkBlock (R ∪ U) code 25 options25 384 16=true := by decide +kernel
private theorem block25_25 : checkBlock (R ∪ U) code 25 options25 400 16=true := by decide +kernel
private theorem block25_26 : checkBlock (R ∪ U) code 25 options25 416 16=true := by decide +kernel
private theorem block25_27 : checkBlock (R ∪ U) code 25 options25 432 16=true := by decide +kernel
private theorem block25_28 : checkBlock (R ∪ U) code 25 options25 448 16=true := by decide +kernel
private theorem block25_29 : checkBlock (R ∪ U) code 25 options25 464 16=true := by decide +kernel
private theorem block25_30 : checkBlock (R ∪ U) code 25 options25 480 16=true := by decide +kernel
private theorem block25_31 : checkBlock (R ∪ U) code 25 options25 496 16=true := by decide +kernel
theorem check25 : checkRow (R ∪ U) code 25 options25=true := by
  apply combine (R ∪ U) code 25 options25 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block25_0
  · exact block25_1
  · exact block25_2
  · exact block25_3
  · exact block25_4
  · exact block25_5
  · exact block25_6
  · exact block25_7
  · exact block25_8
  · exact block25_9
  · exact block25_10
  · exact block25_11
  · exact block25_12
  · exact block25_13
  · exact block25_14
  · exact block25_15
  · exact block25_16
  · exact block25_17
  · exact block25_18
  · exact block25_19
  · exact block25_20
  · exact block25_21
  · exact block25_22
  · exact block25_23
  · exact block25_24
  · exact block25_25
  · exact block25_26
  · exact block25_27
  · exact block25_28
  · exact block25_29
  · exact block25_30
  · exact block25_31

end PlaneResearch.CompactEight
