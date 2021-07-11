/-
# Propositions as Types. 
In this file, we shall be introduced to the paradigm of 
*Propositions as Types* and how they are handled in Lean. 
We shall also use this oppurtunity to get familiar with 
Lean's syntax.  

Acknowledgements : Heavily borrowed from Jalex Stark and
Apurva Nakade's tutorial. 

Import commands go right at the top of a Lean file.
-/

import data.nat.pow
import data.nat.prime 

/- 
  Before that, let us delve into type theory.
 *All* objects in Lean have a *type*.
  Things which have a type are called *terms*. 
  This simple stratification is more powerful than you may first think.
  You can query the type of a term using `#check`. 

  Inspect the following commands:
-/

#check 1
#check ℕ -- type using \nat 
#check Type 
#check Type 1 -- the number indicates a *universe level*
#check and
#check tt 
#check ff


/- 
  Here is an important type. The type of all propositions. 
  Roughly speaking, a proposition is something which can be
  subjected to a proof. 
-/
#check Prop 

/-
In type theory, "a has type A" is written as "a:A".
You can read this in two ways: 

  (1) a belongs to the set A 
  (2) a is a proof of A

Here are some silly propositions. All of these are terms of type Prop. 
-/

#check 1 + 1 = 2 -- equality
#check ∀ (x : ℕ), x = 10
#check ∃ (k : ℕ), 10 = 2*k
#check ∀ (x : bool), x = tt ∨ x = ff
#check ∀ (x y : ℕ), x = y → y = x
#check ∀ (x y z n : ℕ), n > 2 → (x*y*z ≠ 0) → (x^n + y^n = z^n)
#check ∃ k : ℕ, 10 = 2*k -- existential quantification
#check ∀ (x : bool), x = tt ∨ x = ff -- disjunction
#check ∀ (x : bool), x = tt ∧ x = ff -- conjunction
#check ∀ (x y : ℕ), x = y → y = x -- implication
#check ¬(1 = 0) -- negation \not 

-- here is a not so silly proposition
-- (XX : State Fermat's Last Theorem/Goldbach) 

/-
As we've said, propositions can be subjected to *(dis)proof*. 
Here is how this is done in Lean: since every term has a type,
and Propositions are types too, we should read their terms as 
their proofs. 

This points to (2) above. 
To repeat ourselves again, we read `p : 1+1 = 2` as `p` is a
proof of the proposition that 1+1 = 2. 
Let us check if our propositions are provable or not.  

We will try to prove more of our silly props later. 

XX : First proof, syntax explanation, term mode/tactic mode.
-/

theorem one_plus_one_two : 1+1 = 1+1 := 
begin
  refl,
end

theorem ten_is_even :  ∃ k m : ℕ, m = 2*k := 
begin
  use 5,
  use 10,
  refl, 
end

theorem bool_thm :  ∀ (x : bool), x = tt ∨ x = ff := 
begin
  assume x, 
  cases x, 
  {
    right, 
    refl,
  },
  {
    sorry,
  }
end 

/- 
# Tactics 

The terms inside the `begin ... end` block you see here are
called *tactics*. 

As soon as you write out a valid lemma and write a `begin ... end` 
below it, Lean wakes up and tries to solve the goal you stated, and
complains if it can't. 

You look at it's complaints and help it along, until it 
complains no more. This is the *interactive* part of interactive
theorem proving. 

The next incantation defines two abstract propositions and adds 
it to the context henceforth. 

-/

namespace tactics

variables (p q : Prop)

/-
``exact``

  If ``p`` is the target of the current goal and
  ``hp`` is a term of type ``p``, then
  ``exact hp,`` will close the goal.


``intro``

  If the target of the current goal is a function ``p → q``, then
  ``intro hp,`` will produce a hypothesis
  ``hp : P`` and change the target to  ``q``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

-/

theorem tautology' (hp : p) : p :=
begin
  exact hp,
end

theorem tautology'' : p → p :=
begin
  assume hp, 
  exact hp,
end

example : (p → (q → p)) :=
begin
  assume hp, 
  assume hq,
  exact hp,
end

-- Can you find two different ways of proving the following?
example (p q : Prop) : ((q → p) → (q → p)) :=
begin
  sorry,
end

/-

``have``

  If ``f`` is a term of type ``p → q`` and
  ``hp`` is a term of type ``p``, then
  ``have hq := f(hp),`` creates the hypothesis ``hq : q`` .


``apply``

  If the target of the current goal is ``q`` and
  ``f`` is a term of type ``p → q``, then
  ``apply f,`` changes target to ``p``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

-/

example (p q r : Prop) (hp : p) (f : p → q) (g : q → r) : r :=
begin
  have hq : q,
  { 
    exact (f hp),
  },
  exact (g hq),
end

example (p q r : Prop) (hp : p) (f : p → q) (g : q → r) : r :=
begin
  apply g, 
  apply f, 
  exact hp,
end


theorem quux (P Q R S T U: Type)
(hpq : P → Q)
(hqr : Q → R)
(hrs : R → S)
(hst : S → T)
(htu : T → U)
: P → U :=
begin
  assume hp,
  apply htu,
  apply hst,
  apply hrs,
  apply hqr,
  apply hpq,
  exact hp,
end

#print quux

/-

``cases``

  ``cases`` is a general tactic that breaks up complicated terms.
  If ``hpq`` is a term of type ``P ∧ Q`` or ``P ∨ Q`` or ``P ↔ Q``, 
  then use ``cases hpq with hp hq,``.

``split``

  If the target of the current goal is ``P ∧ Q`` or ``P ↔ Q``, 
  then use ``split,``.

``left``/``right``

  If the target of the current goal is ``P ∨ Q``, then use
  either ``left,`` or ``right,`` (choose wisely).

``exfalso``

  Changes the target of the current goal to ``false``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

-/

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  assume hpq,
  split,
  {
    cases hpq with hp hq,
    exact hq,
  },
  {
    cases hpq with hp hq,
    exact hp,
  }
end

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  assume hpq, -- this is a comment in Lean
  split,
  all_goals {
    cases hpq with hp hq,
    assumption,
  },
end

/- This is another comment. -/
example (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
  assume hpq, 
  cases hpq,
  {
    right,
    exact hpq,
  },
  {
    left,
    exact hpq,
  }
end

#check @false.elim

example (P Q R : Prop) : P ∧ false ↔ false :=
begin
  split,
  {
    assume hpf,
    cases hpf with hp hf,
    exact hf,
  },
  {
    assume hf,
    exfalso, 
    exact hf,
  }
end

theorem principle_of_explosion (P Q : Prop) : P ∧ ¬ P → Q :=
begin
  sorry,
end

/-

``exfalso``

  Changes the target of the current goal to ``false``.

``push_neg``

  ``push_neg,`` simplifies negations in the target.
  You can push negations across a hypothesis ``hp : P`` using
  ``push_neg at hp,``.


``contrapose!``

  If the target of the current goal is  ``P → Q``,
  then ``contrapose!,`` changes the target to  ``¬ Q → ¬ P``.

  If the target of the current goal is ``Q`` and
  one of the hypotheses is ``hp : P``, then
  ``contrapose! hp,`` changes the target to  ``¬ P`` and
  changes the hypothesis to ``hp : ¬ Q``.


Delete the ``sorry,`` below and replace them with a legitimate proof.

-/

theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P:=
begin
  sorry,
end

theorem contrapositive_converse (P Q : Prop) : (¬Q → ¬P) → (P → Q) :=
begin
  sorry,
end

example (P : Prop) : ¬ P → ¬ ¬ ¬ P :=
begin
  sorry,
end

theorem principle_of_explosion' (P Q : Prop) : P → (¬ P → Q) :=
begin
  sorry,
end

end tactics




/- 
  Using the tactics above, let's try to prove some of the 
  silly propositions we wrote out before:
   
  ∀ (x : ℕ), x = 10 -- universal quantification
  ∃ k : ℕ, 10 = 2*k -- existential quantification
  ∀ (x : bool), x = tt ∨ x = ff -- disjunction
  ∀ (x : bool), x = tt ∧ x = ff -- conjunction
  ∀ (x y : ℕ), x = y → y = x -- implication
  ¬(1 = 0) -- negation

-/
example : ∀ (x : bool), x = tt ∨ x = ff := 
begin
  intros x, -- pick an arbitrary boolean x
  cases x, -- prove the goal two cases: when x is true and when x is false.
  {
    -- we are in the false branch now
    right,
    refl,
  },
  {
    -- we are in the true branch now
    left,
    refl,
  }
end

/- 
Lemmas and theorems can be named so that they can be referred to in future proofs. 
-/

lemma ten_even : ∃ k : ℕ, 10 = 2*k := 
begin
  use 5,
  refl,
end

#check ten_even -- ten_even is a proof that `∃ k : ℕ, 10 = 2*k`
#check ∃ k : ℕ, 10 = 2*k -- which is a proposition

/-
Prove these:
-/
-- Use rw.
lemma eq_symm : ∀ (x y : ℕ), x = y → y = x := 
begin
  assume x y Hxy,
  rewrite Hxy,
end

-- XX: Show what proving a negation means. Use injection. 
lemma one_ne_zero' : ¬(1 = 0) := 
begin
  assume onezero,
  injection onezero,
end



/-
# Exercises

Using the tactics from above, try to prove as many of the 
following as you can:
-/
namespace exercises 

variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry

end exercises
