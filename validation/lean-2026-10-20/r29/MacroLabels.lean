import SourceMatrices

namespace Erdos670R29
set_option maxHeartbeats 3000000

lemma sourceD_bounds (A B : Fin 6) (hAB : A < B) :
    (9709/500 : ℝ) ≤ sourceD A B ∧ sourceD A B ≤ (707/20 : ℝ) := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceD,labels] at *

lemma sourceD_spacing (A B C D : Fin 6) (hAB : A < B) (hCD : C < D)
    (hne : (A,B) ≠ (C,D)) : (569/500 : ℝ) ≤ |sourceD A B-sourceD C D| := by
  fin_cases A <;> fin_cases B <;> norm_num at hAB
  all_goals fin_cases C <;> fin_cases D <;> norm_num at hCD
  all_goals norm_num [sourceD,labels] at *

#print axioms sourceD_bounds
#print axioms sourceD_spacing
end Erdos670R29
