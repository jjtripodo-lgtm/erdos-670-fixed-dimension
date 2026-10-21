import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossScalar

/-! Exhaustive cross-edge separation for the exact orthogonal-circle metric.
The digit arrays may vary with the cluster. The macro-edge labels only enter
through their baseline separation, so any proved injective colex code applies. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5CrossDigit (s : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  s^2*(k : ℝ)*f i + s*g j

noncomputable def pass5DigitBudget (s h : ℝ) (k : ℕ) : ℝ := s*(s*(k : ℝ)+1)*h

/-- The full two-digit perturbation is bounded by the manuscript's exact budget. -/
theorem pass5CrossDigit_bound (s h : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ)
    (hs : 0 ≤ s) (hf : |f i| ≤ h) (hg : |g j| ≤ h) :
    |pass5CrossDigit s k f g i j| ≤ pass5DigitBudget s h k := by
  obtain ⟨hfl,hfu⟩ := abs_le.mp hf
  obtain ⟨hgl,hgu⟩ := abs_le.mp hg
  have hc : 0 ≤ s^2*(k : ℝ) := by positivity
  have h₀ := mul_le_mul_of_nonneg_left hfl hc
  have h₁ := mul_le_mul_of_nonneg_left hfu hc
  have h₂ := mul_le_mul_of_nonneg_left hgl hs
  have h₃ := mul_le_mul_of_nonneg_left hgu hs
  unfold pass5CrossDigit pass5DigitBudget
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Fine and carry steps separate all distinct digit pairs on one macro edge. -/
theorem pass5_one_macro_separated (s τ h lam ν : ℝ) (k : ℕ)
    (f g : ℕ → ℝ) (hk : 0 < k) (hs : 0 < s) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hf : ∀ i, i < k → |f i| ≤ h) (hg : ∀ j, j < k → |g j| ≤ h)
    (hfstep : ∀ i, i+1 < k → lam ≤ f (i+1)-f i)
    (hgstep : ∀ j, j+1 < k → lam ≤ g (j+1)-g j)
    (hbudget : 2*pass5DigitBudget s h k ≤ (1-τ^2)*ν)
    (hfine : 1 ≤ τ*s*lam) (hcarry : 1 ≤ τ*(s^2*(k : ℝ)*lam-2*s*h))
    {i j u v : ℕ} (hi : i < k) (hj : j < k) (hu : u < k) (hv : v < k)
    (hne : (i,j) ≠ (u,v)) :
    1 ≤ |pass5Phi ν (pass5CrossDigit s k f g i j) -
      pass5Phi ν (pass5CrossDigit s k f g u v)| := by
  let D : ℕ → ℕ → ℝ := fun a b => pass5Phi ν (pass5CrossDigit s k f g a b)
  have hbound (a b : ℕ) (ha : a < k) (hb : b < k) :=
    pass5CrossDigit_bound s h k f g a b hs.le (hf a ha) (hg b hb)
  have hFine : ∀ a, a < k → ∀ b, b+1 < k → 1 ≤ D a (b+1)-D a b := by
    intro a ha b hb
    have hb0 : b < k := by omega
    have hd := mul_le_mul_of_nonneg_left (hgstep b hb) hs.le
    have ht : s*lam ≤ pass5CrossDigit s k f g a (b+1)-pass5CrossDigit s k f g a b := by
      unfold pass5CrossDigit
      nlinarith only [hd]
    have hmono : pass5CrossDigit s k f g a b ≤ pass5CrossDigit s k f g a (b+1) := by
      nlinarith [mul_nonneg hs.le hlam]
    have hslope := (pass5Phi_secant ν τ (pass5DigitBudget s h k)
      (pass5CrossDigit s k f g a b) (pass5CrossDigit s k f g a (b+1))
      hν hτ hτ1 (hbound a b ha hb0) (hbound a (b+1) ha hb) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hfine]
  have hCarry : ∀ a, a+1 < k → 1 ≤ D (a+1) 0-D a (k-1) := by
    intro a ha
    have ha0 : a < k := by omega
    have hlast : k-1 < k := by omega
    have hc : 0 ≤ s^2*(k : ℝ) := by positivity
    have hfGap := mul_le_mul_of_nonneg_left (hfstep a ha) hc
    have hgLo := mul_le_mul_of_nonneg_left (abs_le.mp (hg 0 hk)).1 hs.le
    have hgHi := mul_le_mul_of_nonneg_left (abs_le.mp (hg (k-1) hlast)).2 hs.le
    have ht : s^2*(k : ℝ)*lam-2*s*h ≤
        pass5CrossDigit s k f g (a+1) 0-pass5CrossDigit s k f g a (k-1) := by
      unfold pass5CrossDigit
      nlinarith only [hfGap, hgLo, hgHi]
    have hguardpos : 0 < s^2*(k : ℝ)*lam-2*s*h := by nlinarith
    have hmono : pass5CrossDigit s k f g a (k-1) ≤ pass5CrossDigit s k f g (a+1) 0 := by
      linarith
    have hslope := (pass5Phi_secant ν τ (pass5DigitBudget s h k)
      (pass5CrossDigit s k f g a (k-1)) (pass5CrossDigit s k f g (a+1) 0)
      hν hτ hτ1 (hbound a (k-1) ha0 hlast) (hbound (a+1) 0 ha hk) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hcarry]
  exact rectangular_all_pairs_separated D k k hk hFine hCarry hi hj hu hv hne

/-- Distinct macro baselines remain separate after the two exact displacements. -/
theorem pass5_different_macro_separated (ν μ τ H T U S : ℝ)
    (hν : 0 < ν) (hμ : 0 < μ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hT : |T| ≤ H) (hU : |U| ≤ H)
    (hbν : 2*H ≤ (1-τ^2)*ν) (hbμ : 2*H ≤ (1-τ^2)*μ)
    (hbase : S ≤ |ν-μ|) (hguard : 1 ≤ S-2*H/τ) :
    1 ≤ |pass5Phi ν T-pass5Phi μ U| := by
  have hdν := pass5Phi_displacement ν τ H T hν hτ hτ1 hT hbν
  have hdμ := pass5Phi_displacement μ τ H U hμ hτ hτ1 hU hbμ
  have htri₀ := abs_sub_le ν (pass5Phi ν T) μ
  have htri₁ := abs_sub_le (pass5Phi ν T) (pass5Phi μ U) μ
  rw [abs_sub_comm ν (pass5Phi ν T)] at htri₀
  have hid : 2*H/τ = 2*(H/τ) := by ring
  linarith

/-- All cross pairs: exhaustive same-macro and different-macro cases.
The only macro-code hypothesis is separation of the two baselines when their
ordered cluster pairs differ. This is discharged by any injective integer code. -/
theorem pass5_cross_pairs_separated {ι : Type*}
    (f : ι → ℕ → ℝ) (ν : ι → ι → ℝ) (s τ h lam S : ℝ) (k : ℕ)
    (hk : 0 < k) (hs : 0 < s) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hlam : 0 ≤ lam)
    (hf : ∀ A i, i < k → |f A i| ≤ h)
    (hfstep : ∀ A i, i+1 < k → lam ≤ f A (i+1)-f A i)
    (hfine : 1 ≤ τ*s*lam) (hcarry : 1 ≤ τ*(s^2*(k : ℝ)*lam-2*s*h))
    (hmacro : 1 ≤ S-2*pass5DigitBudget s h k/τ)
    (A B C D : ι) (hν : 0 < ν A B) (hμ : 0 < ν C D)
    (hbν : 2*pass5DigitBudget s h k ≤ (1-τ^2)*(ν A B))
    (hbμ : 2*pass5DigitBudget s h k ≤ (1-τ^2)*(ν C D))
    (hbase : (A,B) ≠ (C,D) → S ≤ |ν A B-ν C D|)
    {i j u v : ℕ} (hi : i < k) (hj : j < k) (hu : u < k) (hv : v < k)
    (hne : (A,B,i,j) ≠ (C,D,u,v)) :
    1 ≤ |pass5Phi (ν A B) (pass5CrossDigit s k (f A) (f B) i j) -
      pass5Phi (ν C D) (pass5CrossDigit s k (f C) (f D) u v)| := by
  by_cases hp : (A,B) = (C,D)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
    apply pass5_one_macro_separated s τ h lam (ν A B) k (f A) (f B)
      hk hs hτ hτ1 hlam hν (hf A) (hf B) (hfstep A) (hfstep B) hbν hfine hcarry
      hi hj hu hv
    intro hij
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
    exact hne rfl
  · exact pass5_different_macro_separated (ν A B) (ν C D) τ
      (pass5DigitBudget s h k) _ _ S hν hμ hτ hτ1
      (pass5CrossDigit_bound s h k (f A) (f B) i j hs.le (hf A i hi) (hf B j hj))
      (pass5CrossDigit_bound s h k (f C) (f D) u v hs.le (hf C u hu) (hf D v hv))
      hbν hbμ (hbase hp) hmacro

/-- Distinct natural macro labels give a full scale-sized baseline gap. -/
theorem pass5_integer_baselines_separated (S K : ℝ) (a b : ℕ)
    (hS : 0 ≤ S) (hab : a ≠ b) :
    S ≤ |S*(K+(a : ℝ)+1)-S*(K+(b : ℝ)+1)| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hh : (a : ℝ)+1 ≤ b := by exact_mod_cast h
    have hm := mul_le_mul_of_nonneg_left hh hS
    have habs := le_abs_self (S*(K+(b : ℝ)+1)-S*(K+(a : ℝ)+1))
    rw [abs_sub_comm] at habs
    nlinarith only [hm, habs]
  · have hh : (b : ℝ)+1 ≤ a := by exact_mod_cast h
    have hm := mul_le_mul_of_nonneg_left hh hS
    have habs := le_abs_self (S*(K+(a : ℝ)+1)-S*(K+(b : ℝ)+1))
    nlinarith only [hm, habs]

#print axioms pass5_cross_pairs_separated
#print axioms pass5_integer_baselines_separated
end Erdos488.Geometry.SeparatedDistances.FixedDimension
