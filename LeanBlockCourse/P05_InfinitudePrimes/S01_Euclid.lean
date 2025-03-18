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


Step 3: Write down the formal statement (a') in Lean using these
types and properties.

Step 4: Take the written proof above, segment it into individual steps,
turn those into pseudo-code and fill in any logical gaps that might occurr.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

theorem euclid_inf_primes (S : Finset ℕ) : ∃ (p : ℕ), p ∉ S ∧ p.Prime := by
  -- For any finite set {p_1, ..., p_r} of primes, consider
  -- the number n = p_1 p_2 ··· p_r + 1. This n has a prime
  -- divisor p. But p is not one of the p_i: otherwise p
  -- would be a divisor of n and of the product p_1 p_2 ··· p_r,
  -- and thus also of the difference n − p_1 p_2 ··· p_r = 1,
  -- which is impossible. So a finite set {p_1, ..., p_r}
  -- cannot be the collection of all prime numbers
  sorry
