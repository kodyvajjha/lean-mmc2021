import tactic

namespace myeven


def is_even (n : ℕ) := ∃ p : ℕ, n = 2*p 

theorem inf_many_evens : ∀ n:ℕ, ∃ k : ℕ, (k > n) ∧ (is_even k) := 
begin
  assume n, -- assume an arbitrary n
  use (2*(n+1)),
  split,
  {
    linarith,
  },
  {
    unfold is_even,
    use (n+1),
  }
end 


end myeven