import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossSeparation

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def crossDigit (sig eta : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  sig*(k : ℝ)*f i + eta*g j

noncomputable def digitBudget (sig eta h : ℝ) (k : ℕ) : ℝ := (sig*(k : ℝ)+eta)*h

/-- The full two-digit perturbation is bounded by the manuscript's exact budget. -/
theorem crossDigit_bound (sig eta h : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ)
    (hsig : 0 ≤ sig) (hs : 0 ≤ eta) (hf : |f i| ≤ h) (hg : |g j| ≤ h) :
    |crossDigit sig eta k f g i j| ≤ digitBudget sig eta h k := by
  obtain ⟨hfl,hfu⟩ := abs_le.mp hf
  obtain ⟨hgl,hgu⟩ := abs_le.mp hg
  have hc : 0 ≤ sig*(k : ℝ) := by positivity
  have h₀ := mul_le_mul_of_nonneg_left hfl hc
  have h₁ := mul_le_mul_of_nonneg_left hfu hc
  have h₂ := mul_le_mul_of_nonneg_left hgl hs
  have h₃ := mul_le_mul_of_nonneg_left hgu hs
  unfold crossDigit digitBudget
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Fine and carry steps separate all distinct digit pairs on one macro edge. -/
theorem one_macro_separated (sig eta τ h lam ν : ℝ) (k : ℕ)
    (f g : ℕ → ℝ) (hk : 0 < k) (hsig : 0 < sig) (hs : 0 < eta) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hf : ∀ i, i < k → |f i| ≤ h) (hg : ∀ j, j < k → |g j| ≤ h)
    (hfstep : ∀ i, i+1 < k → lam ≤ f (i+1)-f i)
    (hgstep : ∀ j, j+1 < k → lam ≤ g (j+1)-g j)
    (hbudget : 2*digitBudget sig eta h k ≤ (1-τ^2)*ν)
    (hfine : 1 ≤ τ*eta*lam) (hcarry : 1 ≤ τ*(sig*(k : ℝ)*lam-2*eta*h))
    {i j u v : ℕ} (hi : i < k) (hj : j < k) (hu : u < k) (hv : v < k)
    (hne : (i,j) ≠ (u,v)) :
    1 ≤ |pass5Phi ν (crossDigit sig eta k f g i j) -
      pass5Phi ν (crossDigit sig eta k f g u v)| := by
  let D : ℕ → ℕ → ℝ := fun a b => pass5Phi ν (crossDigit sig eta k f g a b)
  have hbound (a b : ℕ) (ha : a < k) (hb : b < k) :=
    crossDigit_bound sig eta h k f g a b hsig.le hs.le (hf a ha) (hg b hb)
  have hFine : ∀ a, a < k → ∀ b, b+1 < k → 1 ≤ D a (b+1)-D a b := by
    intro a ha b hb
    have hb0 : b < k := by omega
    have hd := mul_le_mul_of_nonneg_left (hgstep b hb) hs.le
    have ht : eta*lam ≤ crossDigit sig eta k f g a (b+1)-crossDigit sig eta k f g a b := by
      unfold crossDigit
      nlinarith only [hd]
    have hmono : crossDigit sig eta k f g a b ≤ crossDigit sig eta k f g a (b+1) := by
      nlinarith [mul_nonneg hs.le hlam]
    have hslope := (pass5Phi_secant ν τ (digitBudget sig eta h k)
      (crossDigit sig eta k f g a b) (crossDigit sig eta k f g a (b+1))
      hν hτ hτ1 (hbound a b ha hb0) (hbound a (b+1) ha hb) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hfine]
  have hCarry : ∀ a, a+1 < k → 1 ≤ D (a+1) 0-D a (k-1) := by
    intro a ha
    have ha0 : a < k := by omega
    have hlast : k-1 < k := by omega
    have hc : 0 ≤ sig*(k : ℝ) := by positivity
    have hfGap := mul_le_mul_of_nonneg_left (hfstep a ha) hc
    have hgLo := mul_le_mul_of_nonneg_left (abs_le.mp (hg 0 hk)).1 hs.le
    have hgHi := mul_le_mul_of_nonneg_left (abs_le.mp (hg (k-1) hlast)).2 hs.le
    have ht : sig*(k : ℝ)*lam-2*eta*h ≤
        crossDigit sig eta k f g (a+1) 0-crossDigit sig eta k f g a (k-1) := by
      unfold crossDigit
      nlinarith only [hfGap, hgLo, hgHi]
    have hguardpos : 0 < sig*(k : ℝ)*lam-2*eta*h := by nlinarith
    have hmono : crossDigit sig eta k f g a (k-1) ≤ crossDigit sig eta k f g (a+1) 0 := by
      linarith
    have hslope := (pass5Phi_secant ν τ (digitBudget sig eta h k)
      (crossDigit sig eta k f g a (k-1)) (crossDigit sig eta k f g (a+1) 0)
      hν hτ hτ1 (hbound a (k-1) ha0 hlast) (hbound (a+1) 0 ha hk) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hcarry]
  exact rectangular_all_pairs_separated D k k hk hFine hCarry hi hj hu hv hne


#print axioms one_macro_separated
end Erdos670R29
