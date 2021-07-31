import data.set.basic
import data.analysis.filter

/-
  # Sequences
  In this file, we shall try to build some of the theory of sequences. 
  The aim is to get to eventually constant sequences in maximum generality.
-/

namespace seq

-- To us, given a space `α`, a sequence in `α` is a sequence of elements of `α`,
-- say a_0, a_1, ..., a_n, ... In other words, what we are looking for is a function f : ℕ → α
-- No need to define a sequence separately

-- A constant sequence has all values to be the same - that is, for some constant c in `α`,
-- a_i = c for all i

variable {α : Type*} -- `α` is an implicit variable, explicit variables are given by (), and implicit variables are given by {} or []

/-- The constant sequence. -/
--def lambda {α β : Type*} : α → β := λ a, _
def const_seq (c : α) : ℕ → α := λ n, c
#check const_seq (1 : ℤ) 0 -- here Lean is able to identify that the `α` I want to use is indeed the ℕ

-- An eventually constant sequence is one that takes the same value after 
-- a while, that is, given a constant c, ∃ N : ℕ, ∀ i ≥ N, a_i = c.

-- Let us now try to formalize what eventually constant sequences are.
def eventually_constant_seq_1 := 
{ f : ℕ → α | ∃ (c : α) (N : ℕ), ∀ i ≥ N, f i = c }

-- example (0 : eventually_constant_seq_1) :

-- If I have a set of the form s := {x : β | p x}, which is the set of all x in β such that x satisfies the property p. Then, if I choose a term y of type s, y.1 is of type β, and y.2 is a proof that y satisfies the property p.

-- This gives me a set of eventually constant functions on α. Any eventually
-- constant function is a term of this type.
#print eventually_constant_seq_1
-- First create a condition for a sequence to be eventually constant.

def is_eventually_constant (f : ℕ → α) : Prop :=
 set.nonempty { n | ∀ m, n ≤ m → f (nat.succ m) = f m }
-- could have chosen f m = f n as well, which def is better?

def is_eventually_constant' (f : ℕ → α) : Prop :=
 set.nonempty { n | ∀ m, n ≤ m → f m = f n }

structure eventually_const_seq :=
(to_seq : ℕ → α) -- the sequence
(is_ec : is_eventually_constant to_seq) -- proof that the seq is e.c.

-- Define the notion of a limit for an eventually constant sequence
/-- The limit is the value `c` of the e.c. seq, that is limit = N or anything bigger than N -/
noncomputable def sequence_limit' (a : @eventually_constant_seq_1 α) : α :=
classical.some a.2 
-- a.2 says : ∃ (c : α) (N : ℕ), ∀ i ≥ N, a i = c,
-- and classical.some a.2 gives a value c for which ∀ i ≥ N, a i = c.

/-- The minimum N such that a_N = c (use Inf) OR any n such that a_n = c -/
def sequence_limit_index (a : @eventually_constant_seq_1 α) : ℕ := sorry

/-- For all m ≥ index (using the Inf definition), a_m = limit = c. -/
lemma sequence_limit_eq (a : @eventually_constant_seq_1 α) (m : ℕ)
  (hm : sequence_limit_index a ≤ m) : sequence_limit' a = a.1 m := sorry

end seq