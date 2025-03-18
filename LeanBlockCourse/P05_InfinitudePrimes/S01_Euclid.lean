/-
In this section we want to formalize Euclid's proof of the
infinitude of primes as written down by Aigner and Ziegler:

For any finite set {p_1, ..., p_r} of primes, consider
the number n = p_1 p_2 ··· p_r + 1. This n has a prime
divisor p. But p is not one of the p_i: otherwise p
would be a divisor of n and of the product p_1 p_2 ··· p_r,
and thus also of the difference n − p_1 p_2 ··· p_r = 1,
which is impossible. So a finite set {p_1, ..., p_r}
cannot be the collection of all prime numbers

Step 1: Write down the actual statement we want to prove in natural language.

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

Let's use a' (for now)!


Step 2: Gather the types and properties we need to state the theorem.

For `S`: The type `Set` and the property that it is finite.
         Or better just use the type `Finset` (or possibly `List`)

For `p`: The type `Nat` and property `Nat.Prime` to express that it is prime.


Step 3: Write down the formal statement (a) in Lean using these
types and properties.


Step 4: Take the written proof above, segment it into individual steps,
turn those into pseudo-code and fill in any logical gaps that might occurr.


Step 5: Find the following lemmas in mathlib:

* `a + 1 ≠ 1` iff `a ≠ 0` -> `Nat.succ_ne_succ`
* Primes are not zero -> `Nat.Prime.ne_zero`
* `Finset.prod` over non-zero numbers is non-zero -> `Finset.prod_ne_zero_iff`
* Any natural number that is not `1` has a prime divisor -> `Nat.exists_prime_and_dvd`
* Any factor of a product divides the product -> `Finset.dvd_prod_of_mem`
* `1` does not have a prime divisor -> `Nat.Prime.not_dvd_one`
* If `p` divides two numbers, then it divides their difference (or a version that avoids difference) -> `Nat.dvd_add_right`

Step 6: Formalize the proof!
-/

import Mathlib.Data.Nat.Prime.Basic       -- this allows us to use `Nat.Prime`
import Mathlib.Data.Finset.Basic          -- this allows us to use `Finset`
import Mathlib.Algebra.BigOperators.Fin   -- this allows us to use `∏`

#check Nat.succ_ne_succ
#check Nat.Prime.ne_zero
#check Finset.prod_ne_zero_iff
#check Nat.exists_prime_and_dvd
#check Finset.dvd_prod_of_mem
#check Nat.Prime.not_dvd_one
#check Nat.dvd_sub'
#check Nat.dvd_add_iff_left
#check Nat.dvd_add_iff_right
#check Nat.dvd_add_left
#check Nat.dvd_add_right


/-
`Finset.prod (S : Finset α) (f : α → β)` takes two arguments (a finite set `S` and a function `f`)
and computes the product of `f(s)` over all `s ∈ S`. An alternative notation is `(∏ s ∈ S, f s)`.
If no function `f` is provided then this notation uses `id`.
-/

theorem euclid_inf_primes (S : Finset ℕ) (h : ∀ s ∈ S, s.Prime) : ∃ (p : ℕ), p ∉ S ∧ p.Prime := by
  -- (For any finite set `S` of primes)

  -- Consider the number `n = (∏ s ∈ S, s) + 1`.
  
  -- (`n_not_one`)
  -- This `n` is not `1` since `(∏ s ∈ S, s)` is not zero since
  -- it only contains primes, which are never zero, and the product
  -- over non-zero elements is non-zero.

  -- (`p`, `p_dvds_n`, `p_prime`)
  -- `n` has a prime divisor `p` by (`n_not_one`).

  -- (`p_notin_S`)
  -- But `p ∉ S` since otherwise `p` would be a divisor of the product
  -- `∏ s ∈ S, s` by definition and thus also of the difference
  -- `n − ∏ s ∈ S, s = 1` by (`p_dvds_n`) which is impossible since
  -- `1` does not have a prime divisor and `p` is prime by (`p_prime`).

  
  -- (So a finite set `S` cannot be the collection of all prime numbers)
  sorry
