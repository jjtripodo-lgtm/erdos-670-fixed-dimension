import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Erdos670R29

/-- Arbitrarily large cluster sizes have an admissible prime, using only Euclid's theorem. -/
theorem admissible_prime_sizes_unbounded (N : ℕ) :
    ∃ k p : ℕ, max 100 N ≤ k ∧ p.Prime ∧ 6*k < p ∧ 100*p ≤ 101*(6*k) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (6*(max 100 N)+1)
  refine ⟨(p-1)/6, p, ?_, hprime, ?_, ?_⟩ <;> omega

#print axioms admissible_prime_sizes_unbounded
end Erdos670R29
