import CrossDigits
import MacroLabels

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma cross_digit_bound (k i j : ℕ) (hk : 0 < k) (hi : i < k) (hj : j < k) :
    |(138/125)*(k : ℝ)*digit k i+(533/500)*digit k j| ≤
      digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k :=
  crossDigit_bound _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (digit_bound k i hk hi) (digit_bound k j hk hj)

lemma baseline_pos (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B) :
    0 < (k : ℝ)^2*sourceD A B := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD := (sourceD_bounds A B hAB).1
  positivity

lemma cross_lower (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    (37/2 : ℝ)*(k : ℝ)^2 ≤ crossLength k A B i j := by
  have hD := (sourceD_bounds A B hAB).1
  have h := (pass5Phi_range ((k : ℝ)^2*sourceD A B) (971/1000)
    (digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k)
    ((138/125)*(k : ℝ)*digit k i+(533/500)*digit k j)
    (baseline_pos k hk A B hAB) (by norm_num) (by norm_num)
    (cross_digit_bound k i j (by omega) hi hj) (concrete_digit_budget k hk _ hD)).1
  have hm := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  dsimp [crossLength]
  nlinarith

lemma cross_displacement (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    |crossLength k A B i j-(k : ℝ)^2*sourceD A B| ≤
      digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k/(971/1000) :=
  pass5Phi_displacement _ _ _ _ (baseline_pos k hk A B hAB) (by norm_num) (by norm_num)
    (cross_digit_bound k i j (by omega) hi hj)
    (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)

lemma cross_upper (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    crossLength k A B i j < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
  have h := (abs_le.mp (cross_displacement k hk A B hAB i j hi hj)).2
  have hD := (sourceD_bounds A B hAB).2
  have hm := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  unfold digitBudget at h
  nlinarith [sq_nonneg (k : ℝ)]

theorem cross_edges_separated (k : ℕ) (hk : 100 ≤ k)
    (A B C D : Fin 6) (hAB : A < B) (hCD : C < D)
    (i j u v : Fin k) (hne : (A,B,i,j) ≠ (C,D,u,v)) :
    1 ≤ |crossLength k A B i.val j.val-crossLength k C D u.val v.val| := by
  by_cases hmacro : (A,B)=(C,D)
  · have hA : A=C := congrArg Prod.fst hmacro
    have hB : B=D := congrArg Prod.snd hmacro
    subst C
    subst D
    have hpair : (i.val,j.val) ≠ (u.val,v.val) := by
      intro he
      have hi : i=u := Fin.ext (congrArg Prod.fst he)
      have hj : j=v := Fin.ext (congrArg Prod.snd he)
      exact hne (by subst u; subst v; rfl)
    exact one_macro_separated (138/125) (533/500) (971/1000) (((k : ℝ)-1)/2)
      (1-(519/1000)^2/8) ((k : ℝ)^2*sourceD A B) k (digit k) (digit k)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (baseline_pos k hk A B hAB) (fun i hi => digit_bound k i (by omega) hi)
      (fun i hi => digit_bound k i (by omega) hi)
      (fun i hi => digit_step k i (by omega) hi) (fun i hi => digit_step k i (by omega) hi)
      (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)
      concrete_fine (concrete_carry k hk) i.isLt j.isLt u.isLt v.isLt hpair
  · apply pass5_different_macro_separated ((k : ℝ)^2*sourceD A B)
      ((k : ℝ)^2*sourceD C D) (971/1000)
      (digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k) _ _ ((569/500)*(k : ℝ)^2)
      (baseline_pos k hk A B hAB) (baseline_pos k hk C D hCD)
      (by norm_num) (by norm_num)
      (cross_digit_bound k i.val j.val (by omega) i.isLt j.isLt)
      (cross_digit_bound k u.val v.val (by omega) u.isLt v.isLt)
      (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)
      (concrete_digit_budget k hk _ (sourceD_bounds C D hCD).1) ?_ (concrete_macro_gap k hk)
    have h := mul_le_mul_of_nonneg_left (sourceD_spacing A B C D hAB hCD hmacro)
      (sq_nonneg (k : ℝ))
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (k : ℝ))]
    nlinarith only [h]

#print axioms cross_edges_separated
#print axioms cross_lower
#print axioms cross_upper
end Erdos670R29
