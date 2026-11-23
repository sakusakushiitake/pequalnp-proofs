import Research.CompactEightData
import Research.CompactBlocks

namespace PlaneResearch.CompactEight
open PlaneResearch.CompactTables PlaneResearch.CompactBlocks
set_option maxRecDepth 16000
set_option maxHeartbeats 24000000
private theorem block69_0 : checkBlock (R ∪ U) code 69 options69 0 16=true := by decide +kernel
private theorem block69_1 : checkBlock (R ∪ U) code 69 options69 16 16=true := by decide +kernel
private theorem block69_2 : checkBlock (R ∪ U) code 69 options69 32 16=true := by decide +kernel
private theorem block69_3 : checkBlock (R ∪ U) code 69 options69 48 16=true := by decide +kernel
private theorem block69_4 : checkBlock (R ∪ U) code 69 options69 64 16=true := by decide +kernel
private theorem block69_5 : checkBlock (R ∪ U) code 69 options69 80 16=true := by decide +kernel
private theorem block69_6 : checkBlock (R ∪ U) code 69 options69 96 16=true := by decide +kernel
private theorem block69_7 : checkBlock (R ∪ U) code 69 options69 112 16=true := by decide +kernel
private theorem block69_8 : checkBlock (R ∪ U) code 69 options69 128 16=true := by decide +kernel
private theorem block69_9 : checkBlock (R ∪ U) code 69 options69 144 16=true := by decide +kernel
private theorem block69_10 : checkBlock (R ∪ U) code 69 options69 160 16=true := by decide +kernel
private theorem block69_11 : checkBlock (R ∪ U) code 69 options69 176 16=true := by decide +kernel
private theorem block69_12 : checkBlock (R ∪ U) code 69 options69 192 16=true := by decide +kernel
private theorem block69_13 : checkBlock (R ∪ U) code 69 options69 208 16=true := by decide +kernel
private theorem block69_14 : checkBlock (R ∪ U) code 69 options69 224 16=true := by decide +kernel
private theorem block69_15 : checkBlock (R ∪ U) code 69 options69 240 16=true := by decide +kernel
private theorem block69_16 : checkBlock (R ∪ U) code 69 options69 256 16=true := by decide +kernel
private theorem block69_17 : checkBlock (R ∪ U) code 69 options69 272 16=true := by decide +kernel
private theorem block69_18 : checkBlock (R ∪ U) code 69 options69 288 16=true := by decide +kernel
private theorem block69_19 : checkBlock (R ∪ U) code 69 options69 304 16=true := by decide +kernel
private theorem block69_20 : checkBlock (R ∪ U) code 69 options69 320 16=true := by decide +kernel
private theorem block69_21 : checkBlock (R ∪ U) code 69 options69 336 16=true := by decide +kernel
private theorem block69_22 : checkBlock (R ∪ U) code 69 options69 352 16=true := by decide +kernel
private theorem block69_23 : checkBlock (R ∪ U) code 69 options69 368 16=true := by decide +kernel
private theorem block69_24 : checkBlock (R ∪ U) code 69 options69 384 16=true := by decide +kernel
private theorem block69_25 : checkBlock (R ∪ U) code 69 options69 400 16=true := by decide +kernel
private theorem block69_26 : checkBlock (R ∪ U) code 69 options69 416 16=true := by decide +kernel
private theorem block69_27 : checkBlock (R ∪ U) code 69 options69 432 16=true := by decide +kernel
private theorem block69_28 : checkBlock (R ∪ U) code 69 options69 448 16=true := by decide +kernel
private theorem block69_29 : checkBlock (R ∪ U) code 69 options69 464 16=true := by decide +kernel
private theorem block69_30 : checkBlock (R ∪ U) code 69 options69 480 16=true := by decide +kernel
private theorem block69_31 : checkBlock (R ∪ U) code 69 options69 496 16=true := by decide +kernel
theorem check69 : checkRow (R ∪ U) code 69 options69=true := by
  apply combine (R ∪ U) code 69 options69 16 32 (by decide) (by decide)
  intro j
  fin_cases j
  · exact block69_0
  · exact block69_1
  · exact block69_2
  · exact block69_3
  · exact block69_4
  · exact block69_5
  · exact block69_6
  · exact block69_7
  · exact block69_8
  · exact block69_9
  · exact block69_10
  · exact block69_11
  · exact block69_12
  · exact block69_13
  · exact block69_14
  · exact block69_15
  · exact block69_16
  · exact block69_17
  · exact block69_18
  · exact block69_19
  · exact block69_20
  · exact block69_21
  · exact block69_22
  · exact block69_23
  · exact block69_24
  · exact block69_25
  · exact block69_26
  · exact block69_27
  · exact block69_28
  · exact block69_29
  · exact block69_30
  · exact block69_31

end PlaneResearch.CompactEight
