import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block98_0 : checkBlock (R ∪ U) code 98 options98 0 16=true := by decide +kernel
private theorem block98_1 : checkBlock (R ∪ U) code 98 options98 16 16=true := by decide +kernel
private theorem block98_2 : checkBlock (R ∪ U) code 98 options98 32 16=true := by decide +kernel
private theorem block98_3 : checkBlock (R ∪ U) code 98 options98 48 16=true := by decide +kernel
private theorem block98_4 : checkBlock (R ∪ U) code 98 options98 64 16=true := by decide +kernel
private theorem block98_5 : checkBlock (R ∪ U) code 98 options98 80 16=true := by decide +kernel
private theorem block98_6 : checkBlock (R ∪ U) code 98 options98 96 16=true := by decide +kernel
private theorem block98_7 : checkBlock (R ∪ U) code 98 options98 112 16=true := by decide +kernel
private theorem block98_8 : checkBlock (R ∪ U) code 98 options98 128 16=true := by decide +kernel
private theorem block98_9 : checkBlock (R ∪ U) code 98 options98 144 16=true := by decide +kernel
private theorem block98_10 : checkBlock (R ∪ U) code 98 options98 160 16=true := by decide +kernel
private theorem block98_11 : checkBlock (R ∪ U) code 98 options98 176 16=true := by decide +kernel
private theorem block98_12 : checkBlock (R ∪ U) code 98 options98 192 16=true := by decide +kernel
private theorem block98_13 : checkBlock (R ∪ U) code 98 options98 208 16=true := by decide +kernel
private theorem block98_14 : checkBlock (R ∪ U) code 98 options98 224 16=true := by decide +kernel
private theorem block98_15 : checkBlock (R ∪ U) code 98 options98 240 16=true := by decide +kernel
private theorem block98_16 : checkBlock (R ∪ U) code 98 options98 256 16=true := by decide +kernel
private theorem block98_17 : checkBlock (R ∪ U) code 98 options98 272 16=true := by decide +kernel
private theorem block98_18 : checkBlock (R ∪ U) code 98 options98 288 16=true := by decide +kernel
private theorem block98_19 : checkBlock (R ∪ U) code 98 options98 304 16=true := by decide +kernel
private theorem block98_20 : checkBlock (R ∪ U) code 98 options98 320 16=true := by decide +kernel
private theorem block98_21 : checkBlock (R ∪ U) code 98 options98 336 16=true := by decide +kernel
private theorem block98_22 : checkBlock (R ∪ U) code 98 options98 352 16=true := by decide +kernel
private theorem block98_23 : checkBlock (R ∪ U) code 98 options98 368 16=true := by decide +kernel
private theorem block98_24 : checkBlock (R ∪ U) code 98 options98 384 16=true := by decide +kernel
private theorem block98_25 : checkBlock (R ∪ U) code 98 options98 400 16=true := by decide +kernel
private theorem block98_26 : checkBlock (R ∪ U) code 98 options98 416 16=true := by decide +kernel
private theorem block98_27 : checkBlock (R ∪ U) code 98 options98 432 16=true := by decide +kernel
private theorem block98_28 : checkBlock (R ∪ U) code 98 options98 448 16=true := by decide +kernel
private theorem block98_29 : checkBlock (R ∪ U) code 98 options98 464 16=true := by decide +kernel
private theorem block98_30 : checkBlock (R ∪ U) code 98 options98 480 16=true := by decide +kernel
private theorem block98_31 : checkBlock (R ∪ U) code 98 options98 496 16=true := by decide +kernel
theorem check98 : checkRow (R ∪ U) code 98 options98=true := by
  apply combine (R ∪ U) code 98 options98 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block98_0
  · exact block98_1
  · exact block98_2
  · exact block98_3
  · exact block98_4
  · exact block98_5
  · exact block98_6
  · exact block98_7
  · exact block98_8
  · exact block98_9
  · exact block98_10
  · exact block98_11
  · exact block98_12
  · exact block98_13
  · exact block98_14
  · exact block98_15
  · exact block98_16
  · exact block98_17
  · exact block98_18
  · exact block98_19
  · exact block98_20
  · exact block98_21
  · exact block98_22
  · exact block98_23
  · exact block98_24
  · exact block98_25
  · exact block98_26
  · exact block98_27
  · exact block98_28
  · exact block98_29
  · exact block98_30
  · exact block98_31

end PlaneResearch.CompactEight
