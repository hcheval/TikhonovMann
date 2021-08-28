import tactic 
import data.real.basic
import topology.metric_space.basic

open_locale big_operators

#print finset.sum_mono_set_of_nonneg

open finset (range)



example (n m : ℕ) (h : n ≤ m) : finset.range n ≤ finset.range m := finset.range_mono h

lemma nonneg_sub_of_nonneg_sum {x : ℕ → ℝ} {n j : ℕ} (x_nonneg : ∀ i, 0 ≤ x i)
  : 0 ≤ (∑ i in finset.range (n + j), (x i)) - (∑ i in finset.range n, (x i)) := by {
    have h₁ : range n ≤ range (n + j) := sorry,
    have : (∑ i in finset.range n, (x i)) ≤ (∑ i in finset.range (n + j), (x i)) := by {
      have := @finset.sum_mono_set_of_nonneg ℕ ℝ _ x x_nonneg,
      specialize this h₁,
      dsimp only at this,
      exact this,
    },
    exact sub_nonneg.mpr this,
  }


example (a b : ℝ) (h₁ : 0 ≤ a) (h₂ : a ≤ 1) (h₃ : 0 ≤ b): a * b ≤ b := by {
  exact mul_le_of_le_one_left h₃ h₂,
}
example (a : ℝ) (h₁ : 0 ≤ a) (h₂ : a ≤ 1) : 0 ≤ 1 - a := sub_nonneg.mpr h₂

example (a : ℝ) (h₁ : 0 ≤ a) (h₂ : a ≤ 1) : 1 - a ≤ 1 := sub_le_self 1 h₁

example (a b c : ℝ) (h₁ : a ≤ b) : a + c ≤ b + c := add_le_add_right h₁ c

example (a b : ℝ) (h₁ : 0 ≤ a) (h₂ : a ≤ 1) (h₃ : 0 ≤ b) : a * b ≤ b := mul_le_of_le_one_left h₃ h₂

example (a : ℝ) (h : 0 ≤ a) : 0 ≤ 1 / a := one_div_nonneg.mpr h

example (a : ℕ) : 0 ≤ (a : ℝ) := nat.cast_nonneg a

example (a : ℝ) (h : 0 ≤ a) : 0 ≤ a + 1 := by linarith

#check finset.prod_le_one

-- ????????
example (a b c : ℝ) (h : a = b * c) (h₁) : a / b = c := congr_fun (congr_fun h₁ a) b

example (a b c : ℝ) (h : a = b * c) (h₁ : 0 ≠ b) : a / b = c := (cancel_factors.cancel_factors_eq_div (eq.symm h) (ne.symm h₁)).symm

example (a b : ℝ) (h : a ≠ b) : b ≠ a := by library_search

example (a b : ℝ) : dist a b = abs (a - b) := real.dist_eq a b

#check abs_eq_self

example (n m : ℕ) (x : ℕ → ℝ) : ∏ i in range m, x (n + i) = ∏ i in finset.Ico n (n + m), x i := by {
  -- library_search,
}

#check finset.prod_Ico_eq_prod_range

#check @finset.sum_sdiff

#check @finset.Ico.subset_iff

#check finset.range_eq_Ico

example (n m : ℕ) (h : n ≤ m) : n + (m - n) = n + m - n :=
begin 
  exact (nat.add_sub_assoc h n).symm,
end

#check finset.Ico.diff

example (a b c : ℕ) : a = b + (a - b) := 
begin 
  simp,
end

example (n : ℕ) : n ≤ n + 1 := nat.le_succ n

lemma some_ineq (a n m : ℕ) (h : a ≤ n) : a.succ ≤ n + m + 1 := by {
  have h₁ : a + 1 ≤ n + 1 := add_le_add_right h 1,
  have h₂ : n + 1 ≤ n + m + 1 := by {
    rw [add_comm n m, add_assoc],
    exact le_add_self,
  },
  exact le_trans h₁ h₂,
}

-- example (a b : ℕ) : (a : ℝ) = (b : ℝ) → a = b := by {
--   intros h,
--   library_search,
-- }

lemma le_Ico_of_le (a b c : ℕ) (h : a ≤ b) : finset.Ico b c ≤ finset.Ico a c := by {
  dsimp,
  simp [has_subset.subset],
  intros x h₁ h₂,
  exact and.intro (le_trans h h₁) h₂,
}