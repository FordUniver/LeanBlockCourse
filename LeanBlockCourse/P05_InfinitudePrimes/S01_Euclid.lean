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

Step 1: Write down the actual statement we want to prove.
-/

import Mathlib.Data.Nat.Prime.Basic
