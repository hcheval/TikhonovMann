import tactic 
import data.real.basic

open_locale big_operators

#print finset.sum_mono_set_of_nonneg

example (n m : ℕ) (h : n ≤ m) : finset.range n ≤ finset.range m := by library_search

example (x : ℕ → ℝ) (n j : ℕ) (x_nonneg : ∀ i, 0 ≤ x i)
  : 0 ≤ (∑ i in finset.range (n + j), (x i)) - (∑ i in finset.range n, (x i)) := sorry