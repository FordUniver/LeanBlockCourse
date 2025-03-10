import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic

open BigOperators Bool Nat

-- Important: 0! = 1
#eval 0! 
#eval 2! 
#eval 3! 

-- Important: Nat.minFac 0 = 2 and Nat.minFac 1 = 1
#eval Nat.minFac 0 
#eval Nat.minFac 1 
#eval Nat.minFac 3 
#eval Nat.minFac 4 


-- We can write p instead of (p : ℕ) because of type
-- inference: Nat.prime forces p to be a natural number
example (n : ℕ) : ∃ p, Nat.Prime p ∧ n ≤ p := by
  let p := Nat.minFac (n ! + 1)
  use p

  -- We start by showing that p is prime
  have p_prime : Nat.Prime p := by
    apply minFac_prime
    suffices n ! ≠ 0 by simp [this]
    apply factorial_ne_zero

  -- We now have to show that n ≤ p
  suffices n ≤ p by exact ⟨p_prime, this⟩

  -- Assuming the contrary, we would get that ...
  by_contra h
  push_neg at h

  -- ... p cannot divide 1 since it is prime ...
  have p_not_dvd_one : ¬(p ∣ 1) := Nat.Prime.not_dvd_one p_prime

  -- ... but it would have to divide 1 since it divides both n! and n! + 1 ...
  have p_dvd_one : p ∣ 1 := by 

    have p_dvd_n_fac : p ∣ n ! := by
      apply dvd_factorial
      · exact minFac_pos (n ! + 1)
      · exact le_of_succ_le h

    have p_dvd_n_fac_one : p ∣ n ! + 1 := minFac_dvd (n ! + 1)

    exact (Nat.dvd_add_iff_right p_dvd_n_fac).mpr p_dvd_n_fac_one

  -- ... a contradiction!
  contradiction


-- The proof in term mode as it is written in mathlib4
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩
