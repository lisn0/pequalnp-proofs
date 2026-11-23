import L_meta_595_search_sound

namespace Check595

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_0 : branchCheck 0 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_1 : branchCheck 0 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_2 : branchCheck 0 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_0_3 : branchCheck 0 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_0 : branchCheck 0 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_1 : branchCheck 0 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_2 : branchCheck 0 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_1_3 : branchCheck 0 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_0 : branchCheck 0 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_1 : branchCheck 0 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_2 : branchCheck 0 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_2_3 : branchCheck 0 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_0 : branchCheck 0 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_1 : branchCheck 0 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_2 : branchCheck 0 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch0_3_3 : branchCheck 0 3 3 = false := by decide +kernel

private theorem checkedPair0 (j k : Fin 4) : branchCheck 0 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch0_0_0
  · exact branch0_0_1
  · exact branch0_0_2
  · exact branch0_0_3
  · exact branch0_1_0
  · exact branch0_1_1
  · exact branch0_1_2
  · exact branch0_1_3
  · exact branch0_2_0
  · exact branch0_2_1
  · exact branch0_2_2
  · exact branch0_2_3
  · exact branch0_3_0
  · exact branch0_3_1
  · exact branch0_3_2
  · exact branch0_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_0 : branchCheck 1 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_1 : branchCheck 1 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_2 : branchCheck 1 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_0_3 : branchCheck 1 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_0 : branchCheck 1 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_1 : branchCheck 1 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_2 : branchCheck 1 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_1_3 : branchCheck 1 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_0 : branchCheck 1 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_1 : branchCheck 1 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_2 : branchCheck 1 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_2_3 : branchCheck 1 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_0 : branchCheck 1 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_1 : branchCheck 1 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_2 : branchCheck 1 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch1_3_3 : branchCheck 1 3 3 = false := by decide +kernel

private theorem checkedPair1 (j k : Fin 4) : branchCheck 1 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch1_0_0
  · exact branch1_0_1
  · exact branch1_0_2
  · exact branch1_0_3
  · exact branch1_1_0
  · exact branch1_1_1
  · exact branch1_1_2
  · exact branch1_1_3
  · exact branch1_2_0
  · exact branch1_2_1
  · exact branch1_2_2
  · exact branch1_2_3
  · exact branch1_3_0
  · exact branch1_3_1
  · exact branch1_3_2
  · exact branch1_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_0 : branchCheck 2 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_1 : branchCheck 2 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_2 : branchCheck 2 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_0_3 : branchCheck 2 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_0 : branchCheck 2 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_1 : branchCheck 2 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_2 : branchCheck 2 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_1_3 : branchCheck 2 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_0 : branchCheck 2 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_1 : branchCheck 2 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_2 : branchCheck 2 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_2_3 : branchCheck 2 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_0 : branchCheck 2 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_1 : branchCheck 2 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_2 : branchCheck 2 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch2_3_3 : branchCheck 2 3 3 = false := by decide +kernel

private theorem checkedPair2 (j k : Fin 4) : branchCheck 2 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch2_0_0
  · exact branch2_0_1
  · exact branch2_0_2
  · exact branch2_0_3
  · exact branch2_1_0
  · exact branch2_1_1
  · exact branch2_1_2
  · exact branch2_1_3
  · exact branch2_2_0
  · exact branch2_2_1
  · exact branch2_2_2
  · exact branch2_2_3
  · exact branch2_3_0
  · exact branch2_3_1
  · exact branch2_3_2
  · exact branch2_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_0 : branchCheck 3 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_1 : branchCheck 3 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_2 : branchCheck 3 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_0_3 : branchCheck 3 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_0 : branchCheck 3 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_1 : branchCheck 3 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_2 : branchCheck 3 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_1_3 : branchCheck 3 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_0 : branchCheck 3 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_1 : branchCheck 3 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_2 : branchCheck 3 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_2_3 : branchCheck 3 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_0 : branchCheck 3 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_1 : branchCheck 3 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_2 : branchCheck 3 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch3_3_3 : branchCheck 3 3 3 = false := by decide +kernel

private theorem checkedPair3 (j k : Fin 4) : branchCheck 3 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch3_0_0
  · exact branch3_0_1
  · exact branch3_0_2
  · exact branch3_0_3
  · exact branch3_1_0
  · exact branch3_1_1
  · exact branch3_1_2
  · exact branch3_1_3
  · exact branch3_2_0
  · exact branch3_2_1
  · exact branch3_2_2
  · exact branch3_2_3
  · exact branch3_3_0
  · exact branch3_3_1
  · exact branch3_3_2
  · exact branch3_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_0 : branchCheck 4 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_1 : branchCheck 4 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_2 : branchCheck 4 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_0_3 : branchCheck 4 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_0 : branchCheck 4 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_1 : branchCheck 4 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_2 : branchCheck 4 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_1_3 : branchCheck 4 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_0 : branchCheck 4 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_1 : branchCheck 4 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_2 : branchCheck 4 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_2_3 : branchCheck 4 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_0 : branchCheck 4 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_1 : branchCheck 4 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_2 : branchCheck 4 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch4_3_3 : branchCheck 4 3 3 = false := by decide +kernel

private theorem checkedPair4 (j k : Fin 4) : branchCheck 4 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch4_0_0
  · exact branch4_0_1
  · exact branch4_0_2
  · exact branch4_0_3
  · exact branch4_1_0
  · exact branch4_1_1
  · exact branch4_1_2
  · exact branch4_1_3
  · exact branch4_2_0
  · exact branch4_2_1
  · exact branch4_2_2
  · exact branch4_2_3
  · exact branch4_3_0
  · exact branch4_3_1
  · exact branch4_3_2
  · exact branch4_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_0 : branchCheck 5 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_1 : branchCheck 5 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_2 : branchCheck 5 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_0_3 : branchCheck 5 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_0 : branchCheck 5 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_1 : branchCheck 5 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_2 : branchCheck 5 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_1_3 : branchCheck 5 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_0 : branchCheck 5 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_1 : branchCheck 5 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_2 : branchCheck 5 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_2_3 : branchCheck 5 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_0 : branchCheck 5 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_1 : branchCheck 5 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_2 : branchCheck 5 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch5_3_3 : branchCheck 5 3 3 = false := by decide +kernel

private theorem checkedPair5 (j k : Fin 4) : branchCheck 5 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch5_0_0
  · exact branch5_0_1
  · exact branch5_0_2
  · exact branch5_0_3
  · exact branch5_1_0
  · exact branch5_1_1
  · exact branch5_1_2
  · exact branch5_1_3
  · exact branch5_2_0
  · exact branch5_2_1
  · exact branch5_2_2
  · exact branch5_2_3
  · exact branch5_3_0
  · exact branch5_3_1
  · exact branch5_3_2
  · exact branch5_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_0 : branchCheck 6 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_1 : branchCheck 6 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_2 : branchCheck 6 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_0_3 : branchCheck 6 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_0 : branchCheck 6 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_1 : branchCheck 6 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_2 : branchCheck 6 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_1_3 : branchCheck 6 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_0 : branchCheck 6 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_1 : branchCheck 6 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_2 : branchCheck 6 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_2_3 : branchCheck 6 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_0 : branchCheck 6 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_1 : branchCheck 6 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_2 : branchCheck 6 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch6_3_3 : branchCheck 6 3 3 = false := by decide +kernel

private theorem checkedPair6 (j k : Fin 4) : branchCheck 6 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch6_0_0
  · exact branch6_0_1
  · exact branch6_0_2
  · exact branch6_0_3
  · exact branch6_1_0
  · exact branch6_1_1
  · exact branch6_1_2
  · exact branch6_1_3
  · exact branch6_2_0
  · exact branch6_2_1
  · exact branch6_2_2
  · exact branch6_2_3
  · exact branch6_3_0
  · exact branch6_3_1
  · exact branch6_3_2
  · exact branch6_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_0 : branchCheck 7 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_1 : branchCheck 7 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_2 : branchCheck 7 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_0_3 : branchCheck 7 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_0 : branchCheck 7 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_1 : branchCheck 7 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_2 : branchCheck 7 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_1_3 : branchCheck 7 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_0 : branchCheck 7 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_1 : branchCheck 7 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_2 : branchCheck 7 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_2_3 : branchCheck 7 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_0 : branchCheck 7 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_1 : branchCheck 7 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_2 : branchCheck 7 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch7_3_3 : branchCheck 7 3 3 = false := by decide +kernel

private theorem checkedPair7 (j k : Fin 4) : branchCheck 7 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch7_0_0
  · exact branch7_0_1
  · exact branch7_0_2
  · exact branch7_0_3
  · exact branch7_1_0
  · exact branch7_1_1
  · exact branch7_1_2
  · exact branch7_1_3
  · exact branch7_2_0
  · exact branch7_2_1
  · exact branch7_2_2
  · exact branch7_2_3
  · exact branch7_3_0
  · exact branch7_3_1
  · exact branch7_3_2
  · exact branch7_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_0 : branchCheck 8 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_1 : branchCheck 8 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_2 : branchCheck 8 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_0_3 : branchCheck 8 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_0 : branchCheck 8 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_1 : branchCheck 8 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_2 : branchCheck 8 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_1_3 : branchCheck 8 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_0 : branchCheck 8 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_1 : branchCheck 8 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_2 : branchCheck 8 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_2_3 : branchCheck 8 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_0 : branchCheck 8 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_1 : branchCheck 8 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_2 : branchCheck 8 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch8_3_3 : branchCheck 8 3 3 = false := by decide +kernel

private theorem checkedPair8 (j k : Fin 4) : branchCheck 8 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch8_0_0
  · exact branch8_0_1
  · exact branch8_0_2
  · exact branch8_0_3
  · exact branch8_1_0
  · exact branch8_1_1
  · exact branch8_1_2
  · exact branch8_1_3
  · exact branch8_2_0
  · exact branch8_2_1
  · exact branch8_2_2
  · exact branch8_2_3
  · exact branch8_3_0
  · exact branch8_3_1
  · exact branch8_3_2
  · exact branch8_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_0 : branchCheck 9 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_1 : branchCheck 9 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_2 : branchCheck 9 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_0_3 : branchCheck 9 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_0 : branchCheck 9 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_1 : branchCheck 9 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_2 : branchCheck 9 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_1_3 : branchCheck 9 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_0 : branchCheck 9 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_1 : branchCheck 9 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_2 : branchCheck 9 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_2_3 : branchCheck 9 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_0 : branchCheck 9 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_1 : branchCheck 9 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_2 : branchCheck 9 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch9_3_3 : branchCheck 9 3 3 = false := by decide +kernel

private theorem checkedPair9 (j k : Fin 4) : branchCheck 9 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch9_0_0
  · exact branch9_0_1
  · exact branch9_0_2
  · exact branch9_0_3
  · exact branch9_1_0
  · exact branch9_1_1
  · exact branch9_1_2
  · exact branch9_1_3
  · exact branch9_2_0
  · exact branch9_2_1
  · exact branch9_2_2
  · exact branch9_2_3
  · exact branch9_3_0
  · exact branch9_3_1
  · exact branch9_3_2
  · exact branch9_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_0 : branchCheck 10 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_1 : branchCheck 10 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_2 : branchCheck 10 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_0_3 : branchCheck 10 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_0 : branchCheck 10 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_1 : branchCheck 10 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_2 : branchCheck 10 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_1_3 : branchCheck 10 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_0 : branchCheck 10 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_1 : branchCheck 10 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_2 : branchCheck 10 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_2_3 : branchCheck 10 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_0 : branchCheck 10 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_1 : branchCheck 10 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_2 : branchCheck 10 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch10_3_3 : branchCheck 10 3 3 = false := by decide +kernel

private theorem checkedPair10 (j k : Fin 4) : branchCheck 10 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch10_0_0
  · exact branch10_0_1
  · exact branch10_0_2
  · exact branch10_0_3
  · exact branch10_1_0
  · exact branch10_1_1
  · exact branch10_1_2
  · exact branch10_1_3
  · exact branch10_2_0
  · exact branch10_2_1
  · exact branch10_2_2
  · exact branch10_2_3
  · exact branch10_3_0
  · exact branch10_3_1
  · exact branch10_3_2
  · exact branch10_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_0 : branchCheck 11 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_1 : branchCheck 11 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_2 : branchCheck 11 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_0_3 : branchCheck 11 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_0 : branchCheck 11 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_1 : branchCheck 11 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_2 : branchCheck 11 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_1_3 : branchCheck 11 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_0 : branchCheck 11 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_1 : branchCheck 11 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_2 : branchCheck 11 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_2_3 : branchCheck 11 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_0 : branchCheck 11 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_1 : branchCheck 11 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_2 : branchCheck 11 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch11_3_3 : branchCheck 11 3 3 = false := by decide +kernel

private theorem checkedPair11 (j k : Fin 4) : branchCheck 11 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch11_0_0
  · exact branch11_0_1
  · exact branch11_0_2
  · exact branch11_0_3
  · exact branch11_1_0
  · exact branch11_1_1
  · exact branch11_1_2
  · exact branch11_1_3
  · exact branch11_2_0
  · exact branch11_2_1
  · exact branch11_2_2
  · exact branch11_2_3
  · exact branch11_3_0
  · exact branch11_3_1
  · exact branch11_3_2
  · exact branch11_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_0 : branchCheck 12 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_1 : branchCheck 12 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_2 : branchCheck 12 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_0_3 : branchCheck 12 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_0 : branchCheck 12 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_1 : branchCheck 12 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_2 : branchCheck 12 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_1_3 : branchCheck 12 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_0 : branchCheck 12 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_1 : branchCheck 12 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_2 : branchCheck 12 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_2_3 : branchCheck 12 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_0 : branchCheck 12 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_1 : branchCheck 12 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_2 : branchCheck 12 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch12_3_3 : branchCheck 12 3 3 = false := by decide +kernel

private theorem checkedPair12 (j k : Fin 4) : branchCheck 12 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch12_0_0
  · exact branch12_0_1
  · exact branch12_0_2
  · exact branch12_0_3
  · exact branch12_1_0
  · exact branch12_1_1
  · exact branch12_1_2
  · exact branch12_1_3
  · exact branch12_2_0
  · exact branch12_2_1
  · exact branch12_2_2
  · exact branch12_2_3
  · exact branch12_3_0
  · exact branch12_3_1
  · exact branch12_3_2
  · exact branch12_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_0 : branchCheck 13 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_1 : branchCheck 13 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_2 : branchCheck 13 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_0_3 : branchCheck 13 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_0 : branchCheck 13 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_1 : branchCheck 13 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_2 : branchCheck 13 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_1_3 : branchCheck 13 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_0 : branchCheck 13 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_1 : branchCheck 13 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_2 : branchCheck 13 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_2_3 : branchCheck 13 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_0 : branchCheck 13 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_1 : branchCheck 13 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_2 : branchCheck 13 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch13_3_3 : branchCheck 13 3 3 = false := by decide +kernel

private theorem checkedPair13 (j k : Fin 4) : branchCheck 13 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch13_0_0
  · exact branch13_0_1
  · exact branch13_0_2
  · exact branch13_0_3
  · exact branch13_1_0
  · exact branch13_1_1
  · exact branch13_1_2
  · exact branch13_1_3
  · exact branch13_2_0
  · exact branch13_2_1
  · exact branch13_2_2
  · exact branch13_2_3
  · exact branch13_3_0
  · exact branch13_3_1
  · exact branch13_3_2
  · exact branch13_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_0 : branchCheck 14 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_1 : branchCheck 14 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_2 : branchCheck 14 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_0_3 : branchCheck 14 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_0 : branchCheck 14 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_1 : branchCheck 14 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_2 : branchCheck 14 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_1_3 : branchCheck 14 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_0 : branchCheck 14 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_1 : branchCheck 14 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_2 : branchCheck 14 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_2_3 : branchCheck 14 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_0 : branchCheck 14 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_1 : branchCheck 14 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_2 : branchCheck 14 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch14_3_3 : branchCheck 14 3 3 = false := by decide +kernel

private theorem checkedPair14 (j k : Fin 4) : branchCheck 14 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch14_0_0
  · exact branch14_0_1
  · exact branch14_0_2
  · exact branch14_0_3
  · exact branch14_1_0
  · exact branch14_1_1
  · exact branch14_1_2
  · exact branch14_1_3
  · exact branch14_2_0
  · exact branch14_2_1
  · exact branch14_2_2
  · exact branch14_2_3
  · exact branch14_3_0
  · exact branch14_3_1
  · exact branch14_3_2
  · exact branch14_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_0 : branchCheck 15 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_1 : branchCheck 15 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_2 : branchCheck 15 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_0_3 : branchCheck 15 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_0 : branchCheck 15 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_1 : branchCheck 15 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_2 : branchCheck 15 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_1_3 : branchCheck 15 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_0 : branchCheck 15 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_1 : branchCheck 15 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_2 : branchCheck 15 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_2_3 : branchCheck 15 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_0 : branchCheck 15 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_1 : branchCheck 15 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_2 : branchCheck 15 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch15_3_3 : branchCheck 15 3 3 = false := by decide +kernel

private theorem checkedPair15 (j k : Fin 4) : branchCheck 15 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch15_0_0
  · exact branch15_0_1
  · exact branch15_0_2
  · exact branch15_0_3
  · exact branch15_1_0
  · exact branch15_1_1
  · exact branch15_1_2
  · exact branch15_1_3
  · exact branch15_2_0
  · exact branch15_2_1
  · exact branch15_2_2
  · exact branch15_2_3
  · exact branch15_3_0
  · exact branch15_3_1
  · exact branch15_3_2
  · exact branch15_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_0 : branchCheck 16 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_1 : branchCheck 16 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_2 : branchCheck 16 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_0_3 : branchCheck 16 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_0 : branchCheck 16 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_1 : branchCheck 16 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_2 : branchCheck 16 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_1_3 : branchCheck 16 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_0 : branchCheck 16 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_1 : branchCheck 16 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_2 : branchCheck 16 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_2_3 : branchCheck 16 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_0 : branchCheck 16 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_1 : branchCheck 16 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_2 : branchCheck 16 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch16_3_3 : branchCheck 16 3 3 = false := by decide +kernel

private theorem checkedPair16 (j k : Fin 4) : branchCheck 16 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch16_0_0
  · exact branch16_0_1
  · exact branch16_0_2
  · exact branch16_0_3
  · exact branch16_1_0
  · exact branch16_1_1
  · exact branch16_1_2
  · exact branch16_1_3
  · exact branch16_2_0
  · exact branch16_2_1
  · exact branch16_2_2
  · exact branch16_2_3
  · exact branch16_3_0
  · exact branch16_3_1
  · exact branch16_3_2
  · exact branch16_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_0 : branchCheck 17 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_1 : branchCheck 17 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_2 : branchCheck 17 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_0_3 : branchCheck 17 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_0 : branchCheck 17 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_1 : branchCheck 17 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_2 : branchCheck 17 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_1_3 : branchCheck 17 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_0 : branchCheck 17 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_1 : branchCheck 17 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_2 : branchCheck 17 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_2_3 : branchCheck 17 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_0 : branchCheck 17 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_1 : branchCheck 17 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_2 : branchCheck 17 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch17_3_3 : branchCheck 17 3 3 = false := by decide +kernel

private theorem checkedPair17 (j k : Fin 4) : branchCheck 17 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch17_0_0
  · exact branch17_0_1
  · exact branch17_0_2
  · exact branch17_0_3
  · exact branch17_1_0
  · exact branch17_1_1
  · exact branch17_1_2
  · exact branch17_1_3
  · exact branch17_2_0
  · exact branch17_2_1
  · exact branch17_2_2
  · exact branch17_2_3
  · exact branch17_3_0
  · exact branch17_3_1
  · exact branch17_3_2
  · exact branch17_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_0 : branchCheck 18 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_1 : branchCheck 18 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_2 : branchCheck 18 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_0_3 : branchCheck 18 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_0 : branchCheck 18 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_1 : branchCheck 18 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_2 : branchCheck 18 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_1_3 : branchCheck 18 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_0 : branchCheck 18 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_1 : branchCheck 18 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_2 : branchCheck 18 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_2_3 : branchCheck 18 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_0 : branchCheck 18 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_1 : branchCheck 18 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_2 : branchCheck 18 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch18_3_3 : branchCheck 18 3 3 = false := by decide +kernel

private theorem checkedPair18 (j k : Fin 4) : branchCheck 18 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch18_0_0
  · exact branch18_0_1
  · exact branch18_0_2
  · exact branch18_0_3
  · exact branch18_1_0
  · exact branch18_1_1
  · exact branch18_1_2
  · exact branch18_1_3
  · exact branch18_2_0
  · exact branch18_2_1
  · exact branch18_2_2
  · exact branch18_2_3
  · exact branch18_3_0
  · exact branch18_3_1
  · exact branch18_3_2
  · exact branch18_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_0 : branchCheck 19 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_1 : branchCheck 19 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_2 : branchCheck 19 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_0_3 : branchCheck 19 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_0 : branchCheck 19 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_1 : branchCheck 19 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_2 : branchCheck 19 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_1_3 : branchCheck 19 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_0 : branchCheck 19 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_1 : branchCheck 19 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_2 : branchCheck 19 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_2_3 : branchCheck 19 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_0 : branchCheck 19 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_1 : branchCheck 19 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_2 : branchCheck 19 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch19_3_3 : branchCheck 19 3 3 = false := by decide +kernel

private theorem checkedPair19 (j k : Fin 4) : branchCheck 19 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch19_0_0
  · exact branch19_0_1
  · exact branch19_0_2
  · exact branch19_0_3
  · exact branch19_1_0
  · exact branch19_1_1
  · exact branch19_1_2
  · exact branch19_1_3
  · exact branch19_2_0
  · exact branch19_2_1
  · exact branch19_2_2
  · exact branch19_2_3
  · exact branch19_3_0
  · exact branch19_3_1
  · exact branch19_3_2
  · exact branch19_3_3

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_0 : branchCheck 20 0 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_1 : branchCheck 20 0 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_2 : branchCheck 20 0 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_0_3 : branchCheck 20 0 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_0 : branchCheck 20 1 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_1 : branchCheck 20 1 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_2 : branchCheck 20 1 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_1_3 : branchCheck 20 1 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_0 : branchCheck 20 2 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_1 : branchCheck 20 2 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_2 : branchCheck 20 2 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_2_3 : branchCheck 20 2 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_0 : branchCheck 20 3 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_1 : branchCheck 20 3 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_2 : branchCheck 20 3 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem branch20_3_3 : branchCheck 20 3 3 = false := by decide +kernel

private theorem checkedPair20 (j k : Fin 4) : branchCheck 20 j.val k = false := by
  fin_cases j <;> fin_cases k
  · exact branch20_0_0
  · exact branch20_0_1
  · exact branch20_0_2
  · exact branch20_0_3
  · exact branch20_1_0
  · exact branch20_1_1
  · exact branch20_1_2
  · exact branch20_1_3
  · exact branch20_2_0
  · exact branch20_2_1
  · exact branch20_2_2
  · exact branch20_2_3
  · exact branch20_3_0
  · exact branch20_3_1
  · exact branch20_3_2
  · exact branch20_3_3

private theorem checkedBranches (i : Fin 21) (j k : Fin 4) : branchCheck i.val j.val k = false := by
  fin_cases i
  · exact checkedPair0 j k
  · exact checkedPair1 j k
  · exact checkedPair2 j k
  · exact checkedPair3 j k
  · exact checkedPair4 j k
  · exact checkedPair5 j k
  · exact checkedPair6 j k
  · exact checkedPair7 j k
  · exact checkedPair8 j k
  · exact checkedPair9 j k
  · exact checkedPair10 j k
  · exact checkedPair11 j k
  · exact checkedPair12 j k
  · exact checkedPair13 j k
  · exact checkedPair14 j k
  · exact checkedPair15 j k
  · exact checkedPair16 j k
  · exact checkedPair17 j k
  · exact checkedPair18 j k
  · exact checkedPair19 j k
  · exact checkedPair20 j k

end Check595

theorem PEqualNP.Outside.L_meta_595_refutation :=
  PEqualNP.Outside.L_meta_595_of_branch_checks Check595.checkedBranches
