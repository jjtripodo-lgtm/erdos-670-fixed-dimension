import Mathlib.Tactic

namespace EuclideanEpsilonResearch

/-- Exact reciprocal rounding: choose the cluster size before the cluster count. -/
theorem reciprocal_rounding (n m₀ : ℕ) (hm₀ : 0 < m₀) (hn : 4*m₀ ≤ n) :
    let k := n/m₀
    let m := (n+k-1)/k
    4 ≤ k ∧ m₀ ≤ m ∧ m ≤ 2*m₀ ∧ n ≤ m*k ∧ m*k < n+k ∧ m₀*k ≤ n := by
  dsimp only
  let k := n/m₀
  let m := (n+k-1)/k
  change 4 ≤ k ∧ m₀ ≤ m ∧ m ≤ 2*m₀ ∧ n ≤ m*k ∧ m*k < n+k ∧ m₀*k ≤ n
  have hk : 4 ≤ k := (Nat.le_div_iff_mul_le hm₀).2 hn
  have hk0 : 0 < k := by omega
  have hfloor : m₀*k ≤ n := by
    simpa [k, Nat.mul_comm] using Nat.div_mul_le_self n m₀
  have hnext : n < m₀*(k+1) := by
    simpa [k, Nat.mul_comm] using Nat.lt_mul_div_succ n hm₀
  have hsub : n+k-1+1 = n+k := by omega
  have hmprod : m*k ≤ n+k-1 := Nat.div_mul_le_self _ _
  have hmnext : n+k-1 < (m+1)*k := by
    simpa [m, Nat.mul_comm] using Nat.lt_mul_div_succ (n+k-1) hk0
  have hnprod : n ≤ m*k := by nlinarith
  have hmlow : m₀ ≤ m := by nlinarith
  have hmhigh : m ≤ 2*m₀ := by
    have hnum : n+k-1 < (2*m₀+1)*k := by nlinarith
    have : m < 2*m₀+1 := (Nat.div_lt_iff_lt_mul hk0).2 hnum
    omega
  exact ⟨hk,hmlow,hmhigh,hnprod,by omega,hfloor⟩

theorem reciprocal_rounding_ratio (n m k m₀ : ℕ) (hm₀ : 0 < m₀)
    (hsurplus : m*k < n+k) (hkbound : m₀*k ≤ n) :
    (m:ℝ)*(k:ℝ) < (n:ℝ)*(1+1/(m₀:ℝ)) := by
  have hm0 : (0:ℝ) < m₀ := by exact_mod_cast hm₀
  have hs : (m:ℝ)*(k:ℝ) < (n:ℝ)+(k:ℝ) := by exact_mod_cast hsurplus
  have hb : (m₀:ℝ)*(k:ℝ) ≤ n := by exact_mod_cast hkbound
  have hkd : (k:ℝ) ≤ (n:ℝ)/(m₀:ℝ) := by
    apply (le_div_iff₀ hm0).2
    nlinarith
  have he : (n:ℝ)*(1+1/(m₀:ℝ)) = (n:ℝ)+(n:ℝ)/(m₀:ℝ) := by ring
  rw [he]
  linarith

theorem epsilon_coefficient_inflation (ξ : ℝ) (hξ : 0 < ξ) (hξ8 : ξ ≤ 1/8) :
    (1/2+4*ξ)*(1+ξ/1024)^2 < 1/2+5*ξ := by
  have hpoly : (1+ξ/1024)^2 < 1+ξ := by nlinarith [sq_nonneg ξ]
  have hc : 0 < (1/2+4*ξ) := by positivity
  have hc1 : (1/2+4*ξ) ≤ 1 := by linarith
  have hmul := mul_lt_mul_of_pos_left hpoly hc
  nlinarith

theorem epsilon_final_coefficient (ε : ℝ) (hε : 0 < ε) :
    (1/2+5*(ε/8) : ℝ) < 1/2+ε := by linarith

theorem epsilon_dimension_padding (m m₀ : ℕ) (hm : m ≤ 2*m₀) :
    5*m-1 ≤ 10*m₀-1 := by omega

theorem epsilon_ceil_identity (ε : ℝ) :
    ⌈(1024:ℝ)/(ε/8)⌉₊ = ⌈(8192:ℝ)/ε⌉₊ := by
  congr 1
  ring

#print axioms reciprocal_rounding
#print axioms reciprocal_rounding_ratio
#print axioms epsilon_coefficient_inflation
#print axioms epsilon_final_coefficient
#print axioms epsilon_dimension_padding
#print axioms epsilon_ceil_identity

/-- The exact ceiling pays both the macro-size lower bound and reciprocal loss. -/
theorem epsilon_ceil_budget (ξ : ℝ) (hξ : 0 < ξ) :
    0 < ⌈(1024:ℝ)/ξ⌉₊ ∧
    (1024:ℝ)/ξ ≤ (⌈(1024:ℝ)/ξ⌉₊ : ℝ) ∧
    1/(⌈(1024:ℝ)/ξ⌉₊ : ℝ) ≤ ξ/1024 := by
  have hlo : (1024:ℝ)/ξ ≤ (⌈(1024:ℝ)/ξ⌉₊ : ℝ) := Nat.le_ceil _
  have hm0 : (0:ℝ) < (⌈(1024:ℝ)/ξ⌉₊ : ℝ) := (by positivity : (0:ℝ) < 1024/ξ).trans_le hlo
  refine ⟨by exact_mod_cast hm0,hlo,?_⟩
  apply (div_le_iff₀ hm0).2
  have hprod : (1024:ℝ) ≤ (⌈(1024:ℝ)/ξ⌉₊ : ℝ)*ξ := (div_le_iff₀ hξ).1 hlo
  nlinarith

/-- Scalar diameter inflation after reciprocal rounding, with no geometric premise. -/
theorem epsilon_rounded_diameter (ξ : ℝ) (n m k m₀ : ℕ)
    (hξ : 0 < ξ) (hξ8 : ξ ≤ 1/8) (hn : 0 < n) (hm₀ : 0 < m₀)
    (hsurplus : m*k < n+k) (hkbound : m₀*k ≤ n)
    (hrecip : 1/(m₀:ℝ) ≤ ξ/1024) :
    (1/2+4*ξ)*((m:ℝ)*(k:ℝ))^2 < (1/2+5*ξ)*(n:ℝ)^2 := by
  have hratio := reciprocal_rounding_ratio n m k m₀ hm₀ hsurplus hkbound
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hmult := mul_le_mul_of_nonneg_left hrecip hn0.le
  have hratio' : (m:ℝ)*(k:ℝ) < (n:ℝ)*(1+ξ/1024) := by nlinarith
  have hnon : 0 ≤ (m:ℝ)*(k:ℝ) := by positivity
  have hsq : ((m:ℝ)*(k:ℝ))^2 < ((n:ℝ)*(1+ξ/1024))^2 := by nlinarith
  have hc : 0 < (1/2+4*ξ) := by positivity
  have hfirst := mul_lt_mul_of_pos_left hsq hc
  have hsecond := mul_lt_mul_of_pos_right (epsilon_coefficient_inflation ξ hξ hξ8)
    (sq_pos_of_pos hn0)
  nlinarith only [hfirst,hsecond]

#print axioms epsilon_ceil_budget
#print axioms epsilon_rounded_diameter
end EuclideanEpsilonResearch
