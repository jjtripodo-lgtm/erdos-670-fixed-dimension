import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceAllNEmbedding
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Parameters

/-! All-size rounding, deletion, and dimension padding for the fifth pass.
The final theorem here is deliberately conditional on a finite configuration
source: no geometric existence assertion is hidden in this arithmetic layer. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

/-- Exact integer padding at the new 36354 threshold. -/
theorem pass5_all_n_parameters (n : ℕ) (hn : 36354 ≤ n) :
    ∃ k m : ℕ, 2 ≤ k ∧ 18177 ≤ m ∧ m ≤ 27265 ∧
      n ≤ m*k ∧ m*k < n+k ∧ 18177*k ≤ n := by
  let k := n / 18177
  let r := n % 18177
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hk0 : 0 < k := by omega
  have hr : r < 18177 := Nat.mod_lt _ (by norm_num)
  have hnkr : 18177*k+r = n := Nat.div_add_mod n 18177
  have hsub : r+k-1+1 = r+k := by omega
  let q := (r+k-1)/k
  have hqUpper : q ≤ 9088 := by
    have hnum : r+k-1 < (9088+1)*k := by omega
    have := (Nat.div_lt_iff_lt_mul hk0).2 hnum
    change q < 9089 at this
    omega
  have hqmul : q*k ≤ r+k-1 := Nat.div_mul_le_self _ _
  have hnext : r+k-1 < (q+1)*k := by
    simpa [q, Nat.mul_comm] using Nat.lt_mul_div_succ (r+k-1) hk0
  refine ⟨k, 18177+q, hk, Nat.le_add_right _ _, by omega, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · omega

/-- The manuscript's rational rounded coefficient is below the final cap. -/
theorem pass5_rounded_coefficient :
    (24057/32768 : ℝ) * (18178/18177 : ℝ)^2 =
      220816318833/300740452352 ∧
    (24057/32768 : ℝ) * (18178/18177 : ℝ)^2 < 147/200 := by
  norm_num

theorem pass5_rounded_diameter_bound (n m k : ℕ) (hn : 36354 ≤ n)
    (hsurplus : m*k < n+k) (hkbound : 18177*k ≤ n) :
    (24057/32768 : ℝ) * ((m : ℝ)*k)^2 < (147/200 : ℝ)*(n : ℝ)^2 := by
  have hn' : (36354 : ℝ) ≤ n := by exact_mod_cast hn
  have hsize' : (m : ℝ)*(k : ℝ) < (n : ℝ)+(k : ℝ) := by
    exact_mod_cast hsurplus
  have hkbound' : (18177 : ℝ)*(k : ℝ) ≤ n := by exact_mod_cast hkbound
  have hratio : (m : ℝ)*(k : ℝ) < (18178/18177 : ℝ)*n := by linarith
  have hnonneg : 0 ≤ (m : ℝ)*(k : ℝ) := by positivity
  have hrnonneg : 0 ≤ (18178/18177 : ℝ)*n := by positivity
  have hsquare : ((m : ℝ)*(k : ℝ))^2 < ((18178/18177 : ℝ)*n)^2 := by
    nlinarith
  have htarget : (24057/32768 : ℝ)*((18178/18177 : ℝ)*n)^2 <
      (147/200 : ℝ)*(n : ℝ)^2 := by
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < n by linarith)]
  nlinarith

theorem pass5_dimension_bound {m : ℕ} (hm : m ≤ 27265) :
    3*m-1 ≤ 81794 := by omega

/-- Delete surplus points and pad coordinates, retaining all metric properties.
The input configuration and its properties remain explicit hypotheses. -/
theorem pass5_delete_pad {n m k : ℕ}
    (hn : 36354 ≤ n) (hmup : m ≤ 27265)
    (hsize : n ≤ m*k) (hsurplus : m*k < n+k) (hkbound : 18177*k ≤ n)
    (P : Fin m × Fin k → EuclideanSpace ℝ (Fin (3*m-1)))
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : SeparatedConfiguration P)
    (hdiam : ∀ a b, dist (P a) (P b) < (24057/32768 : ℝ)*((m : ℝ)*k)^2) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin 81794),
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      SeparatedConfiguration Q ∧
      (∀ a b, dist (Q a) (Q b) < (147/200 : ℝ)*(n : ℝ)^2) := by
  let f := sourceDeletionEmbedding hsize
  have hf : Function.Injective f := sourceDeletionEmbedding_injective hsize
  have hc : Fintype.card (Fin (3*m-1)) ≤ 81794 := by
    simpa using pass5_dimension_bound hmup
  let B : ℝ := (24057/32768 : ℝ)*((m : ℝ)*k)^2
  have hmin' := source_minimum_restrict P f hf hmin
  have hsep' := source_separated_restrict P f hf hsep
  have hdiam' := source_diameter_restrict P f B (fun a b => (hdiam a b).le)
  obtain ⟨hminQ, hsepQ, hdiamQ⟩ :=
    source_pad_properties hc (P ∘ f) hmin' hsep' B hdiam'
  refine ⟨sourcePadCoordinates hc ∘ P ∘ f, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hminQ
  · simpa only [Function.comp_assoc] using hsepQ
  · intro a b
    exact lt_of_le_of_lt (by simpa only [Function.comp_apply] using hdiamQ a b)
      (pass5_rounded_diameter_bound n m k hn hsurplus hkbound)

/-- Honest all-n endpoint interface. The geometric finite source must still be
supplied; this theorem proves all rounding, deletion, and coordinate padding. -/
theorem pass5_all_n_of_finite_sources
    (hsource : ∀ m k : ℕ, 18177 ≤ m → m ≤ 27265 → 2 ≤ k →
      ∃ P : Fin m × Fin k → EuclideanSpace ℝ (Fin (3*m-1)),
        (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
        SeparatedConfiguration P ∧
        (∀ a b, dist (P a) (P b) < (24057/32768 : ℝ)*((m : ℝ)*k)^2)) :
    ∀ n : ℕ, 36354 ≤ n →
      ∃ Q : Fin n → EuclideanSpace ℝ (Fin 81794),
        (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
        SeparatedConfiguration Q ∧
        (∀ a b, dist (Q a) (Q b) < (147/200 : ℝ)*(n : ℝ)^2) := by
  intro n hn
  obtain ⟨k, m, hk, hm, hmup, hsize, hsurplus, hkbound⟩ := pass5_all_n_parameters n hn
  obtain ⟨P, hmin, hsep, hdiam⟩ := hsource m k hm hmup hk
  exact pass5_delete_pad hn hmup hsize hsurplus hkbound P hmin hsep hdiam

end Erdos488.Geometry.SeparatedDistances.FixedDimension
