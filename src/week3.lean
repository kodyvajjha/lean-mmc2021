import data.set.basic

/-
  # Sequences
  In this file, we shall try to build some of the theory of sequences. 
  The aim is to get to eventually constant sequences in maximum generality.
-/

namespace seq

-- To us, given a space `α`, a sequence in `α` is a sequence of elements of `α`,
-- say a_0, a_1, ..., a_n, ... In other words, what we are looking for is a function f : ℕ → α

-- A constant sequence has all values to be the same - that is, for some constant c in `α`,
-- a_i = c for all i

/-- The constant sequence. -/
def const_seq {α : Type*} (c : α) : ℕ → α := λ n, c

-- An eventually constant sequence is one that takes the same value after 
-- a while, that is, given a constant c, ∃ N : ℕ, ∀ i ≥ N, a_i = c.

-- Let us now try to formalize what eventually constant sequences are.

end seq