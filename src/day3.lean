import data.nat.choose

open_locale big_operators
lemma sum_n_choose (n : ℕ) : ∑ k in finset.range n, k = n.choose 2 :=
begin
  sorry
end

lemma imo_2019_qA3 (f : ℤ → ℤ) (hf : ∀ a b, f(2*a) + 2*f(b) = f(f(a + b))) : 
 f = 0 ∨ ∃ c : ℤ, ∀ x, f x = 2*x + c := sorry