/-
This exercise will guide you through a proof that there are 
infinitely many primes. 
NOTE: You will need to install mathlib for this. 

A good way to confirm if mathlib is installed is to see if 
the following imports work.

This tells Lean to import facts about prime numbers.
-/
import tactic
import data.nat.prime


open nat

/- 
We shall break up the proof into a bunch of lemmas
and use these lemmas in the final proof. 

The first lemma `not_dvd_succ` says that if a ≠ 1 divides b, 
then it does not divide b+1. 

Lemmas/Hints which may be useful for this exercise: 
  * nat.dvd_add_right
  * nat.dvd_one
  * Try to use the rewrite tactic.

(Of course, this is not the only way to prove this exercise.
Look at the file data.nat.prime to see if you can find other
exercises which may help you.

You can browse through 
https://leanprover-community.github.io/mathlib_docs/data/nat/prime.html
for more facts.)
-/

lemma not_dvd_succ {a b : ℕ} (ha : a ≠ 1) (hab : a ∣ b) :
 ¬ (a ∣ b + 1) :=
begin
  sorry,
end  

/- 
 Before we move on to the main theorem, 
 it is good to understand how the `linarith` tactic works.

`linarith` is a high-powered tactic which can be used to
 prove linear (in)equalities.
 
 Read : https://leanprover-community.github.io/mathlib_docs/tactics.html#linarith
-/

example (x : ℕ) (hx₁ : x > 15) (hx₂ : x ≤ 20) : (x < 25) :=
begin
  linarith,
end

example (x y z : ℕ) (h₁ : x > y + 1) (h₂ : y > 2*z + 2): (x > z) := 
begin
  linarith,
end 

/- Shorter proofs can simply use the `by` keyword. -/
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false := by linarith

example(a b d : ℕ) (h: 2*a ≤ 3*b)(h': 1≤ a)(h'': d = 2):
d + a ≤ 5*b := by linarith

/-
Let us try to recall how the proof works:

The factorial n! of a positive integer n is divisible by 
very integer from 2 to n, as it is the product of all of them. 

Hence, n! + 1 is not divisible by any of the integers from 2
to n, inclusive (it gives a remainder of 1 when divided by
each).

Hence n! + 1 is either prime or divisible by a prime larger 
than n. 
In either case, for every positive integer n, there is at
least one prime bigger than n. 
The conclusion is that the number of primes is infinite.

We break up the above sketch into little steps in the proof 
below. 

-/

theorem inf_many_primes : ∀ n : ℕ, ∃ p, p ≥ n ∧ prime p := 
begin
  -- assume an arbitrary n
  assume n, 
  -- define N = n! + 1  
  let N := n.factorial + 1,
  /- Prove first that N ≥ 2. 
     The tactic `linarith` and lemmas `factorial_le`
     and `zero_le` may be helpful.-/
  have Nge2 : N ≥ 2,
  {
    sorry,
  },
  /-
  Next we prove that the numbers from 2 to n divide n!.
   The tactic `linarith` and lemmas `dvd_factorial`
   may be helpful.
  -/
  have dvd₁ : ∀ k n : ℕ, 2 ≤ k ∧ k ≤ n → k ∣ n.factorial,
  {
    sorry,
  },
  /-
  Next we prove that the numbers from 2 to n do NOT divide
  n! + 1. Use the previous lemmas we proved: `dvd₁` and
  `not_dvd_succ`.
  -/
  have dvd₂ : ∀ k n : ℕ, 2 ≤ k ∧ k ≤ n → ¬ (k ∣ n.factorial + 1),
  {
    sorry,
  },
  -- clear some hypothesis to avoid clutter
  clear dvd₁,
  /- 
  The number N := n! + 1 is either prime or not. 
  Note for nerds: This tactic uses *classical* logic.
  It is good to keep this in mind even if you don't care 
  about it. 
  -/
  by_cases (prime N),
  {
    /- 
    in the case where N is prime, we can prove the main goal
    easily. 
    Try using `self_le_factorial` and `linarith`.
    -/
    use N, 
    sorry,
  },
  /-
  In the case where N is not prime, we first add the fact
  that there is a prime which divides it. 
  This is the fact `exists_prime_and_dvd`.
  -/
  have HN := exists_prime_and_dvd Nge2,
  /- Here is another tactic which makes breaking up 
    hypotheses easier. -/
  rcases HN with ⟨p,⟨Hp₁,Hp₂⟩⟩,
  -- Use p now to finish the proof. 
  use p, 
  sorry,
end

/-

Final words of advice: 
* Keep the tactic cheatsheet open next to you if you are lost:
https://leanprover-community.github.io//img/lean-tactics.pdf
* Search for lemmas in mathlib. 
* Always try to get to the goal on paper first. Once that is 
  clear, then move onto formalizing.
-/