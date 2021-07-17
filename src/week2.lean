/-
# Inductive Types
In this file, we will learn about induction and inductive types. 
Along with dependent type theory, they form the core of Lean. We shall 
also see how the natural numbers and integers are defined.

For more information, please refer to Theorem Proving in Lean : 
https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf

-/

#print nat -- this works without any imports! Why?

/- An inductive type is defined using constructors. What are the constructors for 
the natural numbers? -/

inductive nat' : Type
| zero : nat'
| succ : nat' → nat'

open nat'
/- An `instance` is made so that Lean remembers the information it is given regarding 
the given definition. -/
instance : has_zero nat' := ⟨zero⟩
instance : has_one nat' := ⟨succ zero⟩

/- One can use recursion to define addition on the naturals. -/
def add' : nat' → nat' → nat' -- nat' × nat' → nat'
| a zero := a -- a + 0 := a OR add' a 0 := a
| a (succ b) := succ (add' a b) -- a + succ b := succ (a + b)

instance : has_add nat' := ⟨add'⟩ -- nat' has addition

/- Why does `+` work? -/
lemma add_assoc' (a b c : nat') : a + (b + c) = add' (add' a b) c := 
begin
  show a + (b + c) = (a + b) + c,
  induction c with d hd, -- helps with inductive proofs, can also `cases`
  { refl, },
  { show a + (b + d.succ) = (a + b + d).succ,
    rw ←hd, refl, },
end

/- Given, the naturals, how can we now define the integers? -/
inductive int' : Type
| of_nat' : nat' → int' -- identifies every natural number as an integer
| neg_succ_of_nat' : nat' → int' -- takes n to -(1 + n)

/- We need to be able to identify every natural as an integer. We use 
coercions for this purpose, which is denoted by an arrow `↑`. -/
instance : has_coe nat' int' := ⟨int'.of_nat'⟩

protected lemma coe_nat_eq' (n : nat') : ↑n = int'.of_nat' n := rfl

open int'
lemma of_nat_eq_of_nat_iff' (m n : nat') : of_nat' m = of_nat' n ↔ m = n := 
begin
  split,
  { intro h, injection h, },
  { intro h, congr, exact h, },
end

def zero : int' := of_nat' 0
def one  : int' := of_nat' 1

instance : has_zero int' := ⟨of_nat' zero⟩
instance : has_one int' := ⟨one⟩

lemma of_nat_zero' : of_nat' (0 : nat') = (0 : int') := rfl

lemma of_nat_one' : of_nat' (1 : nat') = (1 : int') := rfl

/- Define addition, subtraction, negation and multiplication over 
the integers, and show compatibility with naturals. -/