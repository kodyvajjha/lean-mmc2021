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

/- An `instance` is made so that Lean remembers the information it is given regarding 
the given definition. -/
instance : has_zero nat' := ⟨nat'.zero⟩
instance : has_one nat' := sorry

/- One can use recursion to define addition on the naturals. -/
def add' : nat' → nat' → nat'
| a nat'.zero := a
| a (nat'.succ b) := nat'.succ (add' a b)

instance : has_add nat' := ⟨add'⟩

/- Why does `+` work? -/
lemma add_assoc' (a b c : nat') : a + (b + c) = add' (add' a b) c := sorry

/- Given, the naturals, how can we now define the integers? -/
inductive int' : Type
| of_nat' : nat' → int'
| neg_succ_of_nat' : nat' → int'

/- We need to be able to identify every natural as an integer. We use 
coercions for this purpose, which is denoted by an arrow `↑`. -/
instance : has_coe nat' int' := ⟨int'.of_nat'⟩

protected lemma coe_nat_eq' (n : nat') : ↑n = int'.of_nat' n := rfl

lemma of_nat_eq_of_nat_iff' (m n : nat') : of_nat' m = of_nat' n ↔ m = n := sorry

--open int'
def zero : int' := of_nat' 0
def one  : int' := of_nat' 1

instance : has_zero int' := sorry
instance : has_one int' := sorry

lemma of_nat_zero' : of_nat' (0 : nat') = (0 : int') := sorry

lemma of_nat_one' : of_nat' (1 : nat') = (1 : int') := sorry

/- Define addition, subtraction, negation and multiplication over 
the integers, and show compatibility with naturals. -/