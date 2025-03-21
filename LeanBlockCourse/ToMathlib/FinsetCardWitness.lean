import Mathlib.Data.Finset.Card

-- https://github.com/leanprover-community/mathlib4/pull/23172

namespace Finset

variable {α β : Type*}
variable {s t : Finset α} {a b : α}
variable [DecidableEq α]

theorem sdiff_nonempty_of_card_lt_card (h : #s < #t) : (t \ s).Nonempty := by
  rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
  exact fun h' ↦ h.not_le (card_le_card h')

theorem exists_mem_not_mem_of_card_lt_card (h : #s < #t) :  ∃ e, e ∈ t ∧ e ∉ s := by
  simpa [Finset.Nonempty] using sdiff_nonempty_of_card_lt_card h
