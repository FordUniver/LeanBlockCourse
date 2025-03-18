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

-- example (P : ℕ → Prop) (S : Set ℕ) (s : ℕ) : s ∈ {i ∈ S | P i} → P s := by

#check Finset.mem_filter

example (α : Type*) (S : Finset α) (P : α → Prop) [DecidablePred P] (a : α) : a ∈ {s ∈ S | P s} ↔ a ∈ S ∧ P a := by exact
  Finset.mem_filter

theorem inf_primes_tfae : List.TFAE [
  ∀ (S : Finset ℕ) (h : ∀ s ∈ S, s.Prime), (∃ (p : ℕ), p ∉ S ∧ p.Prime),
  ∀ (S : Finset ℕ), (∃ (p : ℕ), p ∉ S ∧ p.Prime),
  ∀ (r : ℕ), (∃ (S : Finset ℕ), S.card = r+1 ∧ (∀ s ∈ S, s.Prime)),
  ∀ (n : ℕ), (∃ p : ℕ, p.Prime ∧ p ≥ n),
  { p : ℕ | p.Prime }.Infinite,
  ∃ P : ℕ → ℕ, P.Injective ∧ ∀ n, (P n).Prime
    ] := by

  tfae_have 1 → 2 := by
    intro h S
    let S_primes := {s ∈ S | s.Prime} -- the same as`Finset.filter Nat.Prime S`
    obtain ⟨p, p_not_in_S_primes, p_prime⟩ := h S_primes (fun _ h => (Finset.mem_filter.mp h).2)
    use p
    constructor
    · by_contra p_in_S
      have : p ∈ S_primes := by
        rw [Finset.mem_filter]
        exact ⟨p_in_S, p_prime⟩
      contradiction
    · assumption


  tfae_have 2 → 1 := by
    intro h S _
    exact h S

  tfae_have 6 → 3 := by
    intro ⟨P, P_inj, P_image_prime⟩ r
    let R := {n : ℕ | n ≤ r}       -- don't use this ...
    let R' := Finset.range (r + 1) -- ... use this!

    have : Finset.card R' = r + 1 := Finset.card_range (r + 1)

    let S := Finset.image P R'
    use S
    sorry

  tfae_have 5 → 3 := by
    sorry

  tfae_have 6 → 5 := by
    sorry -- is very easy with the right theorem

  tfae_have 5 → 6 := by
    sorry

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
