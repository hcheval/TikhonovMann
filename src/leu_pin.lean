import data.real.basic tactic utils
import rates


namespace leu_pin

section 

  open_locale big_operators
  open finset (range)

  @[reducible] def δ (ψ χ : ℕ → ℕ) (k : ℕ) : ℕ := max (ψ $ 3 * k + 2) ((χ $ 3 * k + 2) + 1)

  variables (a b c s : ℕ → ℝ) (M : ℕ) (ψ χ θ δ₀ : ℕ → ℕ)
  variables (a_nonneg : ∀ (n : ℕ), 0 ≤ a n) (a_lt_one : ∀ n : ℕ, a n < 1) (a_le_one : ∀ (n : ℕ), a n ≤ 1) 
  variables (c_nonneg : ∀ (n : ℕ), 0 ≤ c n) (s_nonneg : ∀ (n : ℕ), 0 ≤ s n)
  variables (main_ineq : ∀ (n : ℕ), s (n + 1) ≤ (1 - a n) * s n + a n * b n + c n)


  include a_nonneg a_le_one c_nonneg s_nonneg main_ineq
  lemma leu_pin_3_2 (p N : ℕ) (h : ∀ n : ℕ, b n ≤ 1 / (p + 1)) :
  ∀ n m : ℕ, N ≤ n → s (n + m + 1) ≤ (∏ i in range (m + 1), (1 - a (n + i))) * s n + (1 - ∏ i in range (m + 1), (1 - a (n + i))) * (1 / (p + 1)) + ∑ i in range (m + 1), c (n + i) :=
  begin 
    intros n m h_N_le_n,
    induction m,
    case zero {
      simp only [add_zero, finset.prod_singleton, sub_sub_cancel, finset.sum_singleton, finset.range_one],
      specialize_all [n] at *,
      nlinarith,
    },
    case succ: m' ih {
      set A := ∏ i in range (m' + 1), (1 - a (n + i)),
    }
  end
  

  lemma leu_pin_3_3
  (M_pos : 0 < M)
  (b_le_inv_k_succ : ∀ k n : ℕ, ψ k ≤ n → b n ≤ 1 / (k + 1))
  (χ_cauchy_modulus_sum_c : is_cauchy_modulus χ (λ n, ∑ i in range (n + 1), c i)) :
  ∀ k m n : ℕ, δ ψ χ k ≤ n →
  s (n + m + 1) ≤ M * (∏ i in range (m + 1), (1 - a (n + i))) + 2 / (3 * k + 2) := 
  sorry 

  omit a_le_one
  include a_lt_one
  lemma leu_pin_3_5
  (M_pos : 0 < M)
  (b_le_inv_k_succ : ∀ k n : ℕ, ψ k ≤ n → b n ≤ 1 / ↑(k + 1))
  (χ_cauchy_modulus_sum_c : is_cauchy_modulus χ (λ n, ∑ i in range (n + 1), c i)) 
  -- (a_lt_one : ∀ n : ℕ, a n < 1) 
  (θ_conv_rate_one_sub_a : is_rate_of_convergence_towards θ (λ n, ∏ i in range (n + 1), (1 - a i)) 0)
  (one_div_delta_le_one_sub_a : ∀ k : ℕ, (1 : ℝ) / (δ₀ k) ≤ ∏ i in range (δ ψ χ k), (1 - a i))
  : is_rate_of_convergence_towards (λ k, (max (θ $ 3 * M * (k + 1) * (δ₀ k) - 1) (δ ψ χ k) + 1)) s 0 
  := 
  begin 
    intros k n h,
    set σ := (λ (k : ℕ), max (θ (3 * M * (k + 1) * δ₀ k - 1)) (δ ψ χ k) + 1) with eq_σ,
    set m := n - δ ψ χ k - 1, 
    have := leu_pin_3_3 a b c s M ψ χ a_nonneg (λ j, le_of_lt (a_lt_one j)) c_nonneg s_nonneg main_ineq M_pos b_le_inv_k_succ χ_cauchy_modulus_sum_c k m (δ ψ χ k) (le_refl _),
    rw [real.dist_0_eq_abs, abs_of_nonneg (s_nonneg _)],
    have := finset.prod_range_add (1 - a) (δ ψ χ k) (m + 1),
  
    -- have : n = δ ψ χ k + m + 1 := sorry,
  end

  
  -- nu ne trebuie 
  -- lemma leu_pin_3_6  
  -- (s_le_M : ∀ n : ℕ, s n ≤ M)
  -- (b_le_inv_k_succ : ∀ p n : ℕ, ψ p ≤ n → b n ≤ 1 / (p + 1)) 
  -- (θ_conv_rate_one_sub_a:  is_rate_of_convergence_towards θ (λ n, ∏ i in range (n + 1), (1 - a i)) 0)
  -- (one_div_delta_le_one_sub_a : ∀ k : ℕ, (1 : ℝ) / (δ k) ≤ ∏ i in range (δ k), (1 - a i)) :
  -- is_rate_of_convergence_towards (λ k, max (θ $ 2 * M * (δ k) * (k + 1) - 1) (δ k) + 1) s 0 :=
  -- sorry


end 

end leu_pin

#check @nat.abs_cast