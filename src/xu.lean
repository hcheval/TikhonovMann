import rates
import leu_pin

open_locale big_operators
open finset (range)

def xu_rate (χ γ δ₀ : ℕ → ℕ) (L : ℕ) (k : ℕ) : ℕ :=
max 
  (γ (3 * L * (k + 1) * (δ₀ k) - 1)) 
  (χ (3 * k + 2) + 1) 
  + 1

open leu_pin (δ)

lemma xu_quantitative
(a c s : ℕ → ℝ) 
(L : ℕ) 
(χ : ℕ → ℕ)
(γ : ℕ → ℕ)
(δ₀ : ℕ → ℕ)
(a0 : ∀ n : ℕ, 0 ≤ a n)
(a1 : ∀ n : ℕ, a n < 1)
(c0 : ∀ n : ℕ, 0 ≤ c n)
(s0 : ∀ n : ℕ, 0 ≤ s n)
(L_pos : 0 < L)
(h : ∀ n : ℕ, s (n + 1) ≤ (1 - a n) * (s n) + c n)
(L_bound_s : ∀ n : ℕ, s n ≤ L)
(χ_cauchy_mod : is_cauchy_modulus χ (λ n, ∑ i in range (n + 1), c i))
(γ_conv_rate : is_rate_of_convergence_towards γ (λ n, ∏ i in range (n + 1), (1 - a i)) 0)
(hδ₀ : ∀ k : ℕ, 1 / (δ₀ k : ℝ) ≤ (∏ i in range ((χ $ 3 * k + 2) + 1), (1 - a i))) :
is_rate_of_convergence_towards (xu_rate χ γ δ₀ L) s 0 := 
begin 
  have δ_of_zero : ∀ k, δ (λ _, 0) χ k = (χ $ 3 * k + 2) + 1 :=  by simp only [forall_const, max_eq_right_iff, zero_le'],
  have := leu_pin.leu_pin_3_5 a (λ _, 0) c s L (λ _, 0) χ γ δ₀ a0 a1 c0 s0 (by simpa) L_pos (λ _ _ _, by { simp only [one_div, inv_nonneg], exact nat.cast_nonneg _ }) χ_cauchy_mod γ_conv_rate hδ₀,
  all_goals {simp_rw [δ_of_zero] at *,},
  exact this,
end

#check nat.cast_nonneg