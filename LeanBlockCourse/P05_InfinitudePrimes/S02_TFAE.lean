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
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Nth
import LeanBlockCourse.ToMathlib.FinsetCardWitness

#check Nat.nth_mem_of_infinite
#check Nat.nth_injective
#check Set.infinite_of_injective_forall_mem
#check Finset.card_image_of_injective
#check Finset.card_image_iff
#check Finset.not_mem_of_max_lt
#check Set.exists_mem_not_mem_of_ncard_lt_ncard


theorem inf_primes_tfae : List.TFAE [
  ∀ (S : Finset ℕ) (h : ∀ s ∈ S, s.Prime), (∃ (p : ℕ), p ∉ S ∧ p.Prime),  -- 1
  ∀ (S : Finset ℕ), (∃ (p : ℕ), p ∉ S ∧ p.Prime),                         -- 2
  ∀ (r : ℕ), (∃ (S : Finset ℕ), S.card = r+1 ∧ (∀ s ∈ S, s.Prime)),       -- 3
  ∀ (n : ℕ), (∃ p : ℕ, p.Prime ∧ p ≥ n),                                  -- 4
  { p : ℕ | p.Prime }.Infinite,                                           -- 5
  ∃ P : ℕ → ℕ, P.Injective ∧ ∀ n, (P n).Prime                             -- 6
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
    clear tfae_1_to_2 tfae_2_to_1

    intro ⟨P, P_inj, P_image_prime⟩ r

    -- Use `Finset.range (r + 1)` not `{n : ℕ | n ≤ r}`!
    let R := Finset.range (r + 1)
    let S := Finset.image P R
    use S

    constructor
    · rw [← Finset.card_range (r + 1)]
      exact Finset.card_image_of_injective R P_inj
    · intro s hs
      obtain ⟨n, n_in_R, Pn_eq_s⟩ := Finset.mem_image.mp hs
      rw [← Pn_eq_s]
      exact P_image_prime n

  tfae_have 6 → 5 := by
    clear tfae_1_to_2 tfae_2_to_1 tfae_6_to_3
    intro ⟨P, P_inj, P_prime⟩

    have P_image : ∀ n, P n ∈ {p | Nat.Prime p} := fun n => P_prime n

    exact Set.infinite_of_injective_forall_mem P_inj P_image

  tfae_have 5 → 6 := by
    clear tfae_1_to_2 tfae_2_to_1 tfae_6_to_3 tfae_6_to_5
    intro h

    let P := Nat.nth Nat.Prime
    use P

    constructor
    · exact Nat.nth_injective h
    · intro n
      exact Nat.nth_mem_of_infinite h n

  tfae_have 2 → 5 := by
    clear tfae_1_to_2 tfae_2_to_1 tfae_6_to_3 tfae_6_to_5 tfae_5_to_6
    intro h

    by_contra hc
    replace hc : {p | Nat.Prime p}.Finite := Set.not_infinite.mp hc
    -- or `simp at hc`

    let S := Set.Finite.toFinset hc
    obtain ⟨p, p_notin_S, p_prime⟩ := h S
    have p_in_S : p ∈ S := (Set.Finite.mem_toFinset hc).mpr p_prime

    contradiction

  tfae_have 4 → 3 := by
    clear tfae_1_to_2 tfae_2_to_1 tfae_6_to_3 tfae_6_to_5 tfae_5_to_6 tfae_2_to_5
    intro h r
    induction' r with r' ih
    · use {2}
      trivial
    · obtain ⟨S, S_card, S_prime⟩ := ih
      have S_card_ne_zero : S.card ≠ 0 := by simp_all
      have S_nonempty : S.Nonempty := Finset.card_ne_zero.mp S_card_ne_zero

      let m := S.max' S_nonempty

      obtain ⟨p, p_prime, p_ge⟩ := h (m + 1)
      have : p ∉ S := by
        by_contra p_in_S
        have p_le_m : p ≤ m := Finset.le_max' S p p_in_S
        have p_nle_m : ¬ (p ≤ m) := Nat.not_le_of_lt p_ge
        contradiction

      let S' := S ∪ {p}
      use S'

      constructor
      · have : Disjoint S {p} := Finset.disjoint_singleton_right.mpr this
        rw [← Finset.card_union_eq_card_add_card] at this
        rw [this, S_card]
        rfl
      · intro s hs
        apply Finset.mem_union.mp at hs
        rcases hs with hs' | hs''
        · exact S_prime s hs'
        · simp_all

  tfae_have 3 → 2 := by
    clear tfae_1_to_2 tfae_2_to_1 tfae_6_to_3 tfae_6_to_5 tfae_5_to_6 tfae_2_to_5 tfae_4_to_3
    intro h S
    obtain ⟨T, T_card, T_prime⟩ := h S.card
    have : ∃ p ∈ T, p ∉ S := Finset.exists_mem_not_mem_of_card_lt_card (by simp_all)
    obtain ⟨p, p_in_T, p_nin_S⟩ := this
    apply T_prime at p_in_T
    use p

  tfae_have 2 → 4 := by
    clear tfae_1_to_2 tfae_2_to_1 tfae_6_to_3 tfae_6_to_5 tfae_5_to_6 tfae_2_to_5 tfae_4_to_3 tfae_3_to_2
    intro h n
    let S := Finset.range n
    obtain ⟨p, p_nin_S, p_prime⟩ := h S
    use p
    constructor
    · assumption
    · by_contra! hc
      have : p ∈ S := Finset.mem_range.mpr hc
      contradiction

  tfae_finish
