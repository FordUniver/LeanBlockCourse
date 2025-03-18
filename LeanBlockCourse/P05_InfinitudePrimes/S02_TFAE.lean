/-
In this section we want to prove the equivalence
of several formulations of the statement "There
are infinitely many primes".

a) Have: Finite set `S` of prime numbers.
   Want: Prime number not in `S`.

a') Have: Finite set `S`.
    Want: Prime number `p` not in `S`.

b) Have: Integer `r`.
   Want: `r + 1` distinct primes.

c) Have: Integer `n`.
   Want: Prime number `p` with `p ≥ n`.

d) Have: The set of all primes `S`.
   Want: `S` has infinite cardinality.

d') Have: -
    Want: An injective function `P` from the natural numbers
          to the natural numbers so that any `P(n)` is prime.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.TFAE

theorem inf_primes_tfae : List.TFAE [
  ∀ (S : Finset ℕ) (h : ∀ s ∈ S, s.Prime), (∃ (p : ℕ), p ∉ S ∧ p.Prime),
  ∀ (S : Finset ℕ), (∃ (p : ℕ), p ∉ S ∧ p.Prime),
  ∀ (r : ℕ), (∃ (S : Finset ℕ), S.card = r+1 ∧ (∀ s ∈ S, s.Prime)),
  ∀ (n : ℕ), (∃ p : ℕ, p.Prime ∧ p ≥ n),
  { p : ℕ | p.Prime }.Infinite,
  ∃ P : ℕ → ℕ, P.Injective ∧ ∀ n, (P n).Prime
    ] := by

  tfae_have 1 → 2 := by
    sorry -- is very easy

  tfae_have 2 → 1 := by
    sorry -- should be pretty easy

  tfae_have 6 → 3 := by
    sorry -- should be pretty easy

  tfae_have 5 → 3 := by
    sorry -- is very easy with the right theorem

  tfae_have 6 → 5 := by
    sorry -- is very easy with the right theorem

  tfae_have 5 → 6 := by
    sorry -- is pretty easy

  tfae_have 2 → 4 := by
    sorry -- is pretty easy

  tfae_have 4 → 2 := by
    sorry -- is okay

  tfae_have 5 → 2 := by
    sorry -- is easy with the right theorem
  
  tfae_have 2 → 5 := by
    sorry -- is okay

  tfae_have 3 → 2 := by
    sorry -- should be easy
    
  tfae_finish
