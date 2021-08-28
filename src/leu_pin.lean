import data.real.basic tactic utils
import rates


namespace leu_pin

section 

  open_locale big_operators
  open finset (range Ico)

  @[reducible] def δ (ψ χ : ℕ → ℕ) (k : ℕ) : ℕ := max (ψ $ 3 * k + 2) ((χ $ 3 * k + 2) + 1)

  variables (a b c s : ℕ → ℝ) (M : ℕ) (ψ χ θ δ₀ : ℕ → ℕ)
  variables (a_nonneg : ∀ (n : ℕ), 0 ≤ a n) (a_lt_one : ∀ n : ℕ, a n < 1) (a_le_one : ∀ (n : ℕ), a n ≤ 1) 
  variables (c_nonneg : ∀ (n : ℕ), 0 ≤ c n) (s_nonneg : ∀ (n : ℕ), 0 ≤ s n)
  variables (main_ineq : ∀ (n : ℕ), s (n + 1) ≤ (1 - a n) * s n + a n * b n + c n)


  include a_nonneg a_le_one c_nonneg s_nonneg main_ineq
  lemma leu_pin_3_2 (p N : ℕ) (h : ∀ n : ℕ, N ≤ n → b n ≤ 1 / (p + 1)) :
  ∀ n m : ℕ, N ≤ n → s (n + m + 1) ≤ (∏ i in range (m + 1), (1 - a (n + i))) * s n + (1 - ∏ i in range (m + 1), (1 - a (n + i))) * (1 / (p + 1)) + ∑ i in range (m + 1), c (n + i) :=
  begin 
    intros n m h_N_le_n,
    induction m,
    case zero {
      simp only [add_zero, finset.prod_singleton, sub_sub_cancel, finset.sum_singleton, finset.range_one],
      specialize_all [n] at *,
      specialize h.n h_N_le_n,
      nlinarith,
    },
    case succ: m ih {
      have one_sub_a_nonneg : 0 ≤ 1 - a (n + m + 1) := sub_nonneg.mpr (a_le_one $ n + m + 1),
      have one_sub_a_le_one : 1 - a (n + m + 1) ≤ 1 := sub_le_self _ (a_nonneg $ n + m + 1),
      set A := ∏ i in range (m + 1), (1 - a (n + i)), 

      have h₁ : (1 - a (n + m + 1)) * A = (∏ i in range (m + 1 + 1), (1 - (a $ n + i))) := by {
        dsimp [A],
        have : (1 - (a $ n + m + 1)) = (λ i, (1 - a (n + i))) (m + 1) := by { dsimp only, refl, },
        rw [this, ←finset.prod_range_succ_comm],
      },

      calc s (n + m.succ + 1) 
          ≤ (1 - (a $ n + m + 1)) * (s $ n + m + 1) + (a $ n + m + 1) * (b $ n + m + 1) + (c $ n + m + 1) : by apply main_ineq
      ... ≤ (1 - (a $ n + m + 1)) * (A * s n + (1 - A) * (1 / (↑p + 1)) + ∑ (i : ℕ) in range (m + 1), c (n + i)) + (a $ n + m + 1) * (b $ n + m + 1) + (c $ n + m + 1) : by nlinarith
      ... ≤ (1 - (a $ n + m + 1)) * (A * s n + (1 - A) * (1 / (↑p + 1)) + ∑ (i : ℕ) in range (m + 1), c (n + i)) + (a $ n + m + 1) * (1 / (↑p + 1)) + (c $ n + m + 1) : by nlinarith [a_nonneg (n + m + 1), h (n + m + 1) (by linarith)]
      ... = (1 - (a $ n + m + 1)) * (A * s n) + (1 - (a $ n + m + 1)) * (1 - A) * (1 / (↑p + 1)) + (1 - (a $ n + m + 1)) * ( ∑ (i : ℕ) in range (m + 1), c (n + i)) + (a $ n + m + 1) * (1 / (↑p + 1)) + (c $ n + m + 1) : by ring 
      ... = (1 - (a $ n + m + 1)) * (A * s n) + ((1 - (a $ n + m + 1)) * (1 - A) + (a $ n + m + 1)) * (1 / (↑p + 1)) + (1 - (a $ n + m + 1)) * ( ∑ (i : ℕ) in range (m + 1), c (n + i)) + (c $ n + m + 1) : by ring 
      ... = (((1 - (a $ n + m + 1)) * A) * s n) + ((1 - (a $ n + m + 1)) * (1 - A) + (a $ n + m + 1)) * (1 / (↑p + 1)) + (1 - (a $ n + m + 1)) * ( ∑ (i : ℕ) in range (m + 1), c (n + i)) + (c $ n + m + 1) : by rw mul_assoc
      ... = ((∏ i in range (m.succ + 1), (1 - (a $ n + i))) * s n) + ((1 - (a $ n + m + 1)) * (1 - A) + (a $ n + m + 1)) * (1 / (↑p + 1)) + (1 - (a $ n + m + 1)) * ( ∑ (i : ℕ) in range (m + 1), c (n + i)) + (c $ n + m + 1) : by rw h₁
      ... = ((∏ i in range (m.succ + 1), (1 - (a $ n + i))) * s n) + ((1 - (a $ n + m + 1)) - (1 - (a $ n + m + 1)) * A + (a $ n + m + 1)) * (1 / (↑p + 1)) + (1 - (a $ n + m + 1)) * ( ∑ (i : ℕ) in range (m + 1), c (n + i)) + (c $ n + m + 1) : by ring
      ... = ((∏ i in range (m.succ + 1), (1 - (a $ n + i))) * s n) + (1 - (1 - (a $ n + m + 1)) * A) * (1 / (↑p + 1)) + (1 - (a $ n + m + 1)) * ( ∑ (i : ℕ) in range (m + 1), c (n + i)) + (c $ n + m + 1) : by ring
      ... = ((∏ i in range (m.succ + 1), (1 - (a $ n + i))) * s n) + (1 - (∏ i in range (m.succ + 1), (1 - (a $ n + i)))) * (1 / (↑p + 1)) + (1 - (a $ n + m + 1)) * ( ∑ (i : ℕ) in range (m + 1), c (n + i)) + (c $ n + m + 1) : by rw h₁
      ... ≤ ((∏ i in range (m.succ + 1), (1 - (a $ n + i))) * s n) + (1 - (∏ i in range (m.succ + 1), (1 - (a $ n + i)))) * (1 / (↑p + 1)) + ∑ i in range (m.succ + 1), c (n + i) : by {
        nth_rewrite 1 finset.sum_range_succ,
        have h₂ : (1 - a (n + m + 1)) * ∑ (i : ℕ) in range (m + 1), c (n + i) ≤ ∑ (x : ℕ) in range (m.succ), c (n + x) := mul_le_of_le_one_left (finset.sum_nonneg (λ i _, c_nonneg $ n + i)) one_sub_a_le_one,
        rw [(show n + m + 1 = n + m.succ, by rw add_assoc), ←add_assoc],
        repeat { rw [add_comm _ (c $ n + m.succ)] },
        repeat { apply add_le_add_left },
        exact h₂,
      }
    }
  end
  

  lemma leu_pin_3_3
  (M_pos : 0 < M)
  (s_le_M : ∀ n, s n ≤ M)
  (b_le_inv_k_succ : ∀ k n : ℕ, ψ k ≤ n → b n ≤ 1 / (k + 1))
  (χ_cauchy_modulus_sum_c : is_cauchy_modulus χ (λ n, ∑ i in range (n + 1), c i)) :
  ∀ k m n : ℕ, δ ψ χ k ≤ n →
  s (n + m + 1) ≤ M * (∏ i in range (m + 1), (1 - a (n + i))) + 2 / (↑(3 * k + 2) + 1):= 
  begin 
    -- intros k m n δ_le_n,
    have h₁ : ∀ k, ψ (3 * k + 2) ≤ δ ψ χ k := λ _, le_max_left _ _,
    have h₂ : ∀ k n, δ ψ χ k ≤ n → ψ (3 * k + 2) ≤ n := λ _ _ δ_le_n, le_trans (h₁ _) δ_le_n,
    have h₃ : ∀ k n, ψ (3 * k + 2) ≤ n → b n ≤ 1 / (↑(3 * k + 2) + 1):= λ k n ψ_le_n, b_le_inv_k_succ _ _ ψ_le_n,
    have h₄ : ∀ k n, δ ψ χ k ≤ n → b n ≤  1 / (↑(3 * k + 2) + 1) := λ k n δ_le_n, h₃ _ _ (h₂ _ _ δ_le_n),
    intros k m n δ_le_n,
    have := leu_pin_3_2 a b c s a_nonneg a_le_one c_nonneg s_nonneg main_ineq (3 * k + 2) (δ ψ χ k) (h₄ k) n m δ_le_n,

    have : 0 ≤ (∏ i in range (m + 1), (1 - (a $ n + i))) := finset.prod_nonneg (λ i _, sub_nonneg.mpr $ a_le_one $ n + i),

    have h₅ : s (n + m + 1) ≤ M * (∏ i in range (m + 1), (1 - (a $ n + i))) + (1 / (↑(3 * k + 2) + 1)) + ∑ i in range (m + 1), c (n + i) :=
    calc s (n + m + 1) 
        ≤ (∏ (i : ℕ) in range (m + 1), (1 - a (n + i))) * M + (1 - ∏ (i : ℕ) in range (m + 1), (1 - a (n + i))) * (1 / (↑(3 * k + 2) + 1)) + ∑ (i : ℕ) in range (m + 1), c (n + i) : by nlinarith [s_le_M n]
    ... ≤ (∏ (i : ℕ) in range (m + 1), (1 - a (n + i))) * M + (1 / (↑(3 * k + 2) + 1)) + ∑ (i : ℕ) in range (m + 1), c (n + i) : by {
      -- have h₀' : (∏ (i : ℕ) in range (m + 1), (1 - a (n + i))) ≤ 1 := finset.prod_le_one (λ i _, sub_nonneg.mpr $ a_le_one $ n + i) (λ i _, sub_le_self 1 $ a_nonneg $ n + i),
      have h₁' : (1 - ∏ (i : ℕ) in range (m + 1), (1 - a (n + i))) ≤ 1 := sub_le_self 1 this,
      have h₂' : (0 : ℝ) ≤ (1 / (↑(3 * k + 2) + 1)) := one_div_nonneg.mpr (by { have : (0 : ℝ) ≤ (↑(3 * k + 2)) := nat.cast_nonneg (3 * k + 2), nlinarith }),
      have : (1 - ∏ (i : ℕ) in range (m + 1), (1 - a (n + i))) * (1 / (↑(3 * k + 2) + 1)) ≤  1 / (↑(3 * k + 2) + 1) := mul_le_of_le_one_left h₂' h₁',
      nlinarith,
    }
    ... ≤ M * (∏ i in range (m + 1), (1 - (a $ n + i))) + (1 / (↑(3 * k + 2) + 1)) + ∑ i in range (m + 1), c (n + i) : by rw [mul_comm _ ↑M],

    have h₆ : (χ $ 3 * k + 2) + 1 ≤ n := le_trans (le_max_right _ _) δ_le_n,

    set r : ℕ := n + m - χ (3 * k + 2),
  
    have h₇ : ∑ i in range (m + 1), c (n + i) ≤ 1 / (↑(3 * k + 2) + 1) :=
    calc ∑ i in range (m + 1), c (n + i) 
        = ∑ i in Ico n (n + m + 1), c i : by {
          have : n + m + 1 - n = m + 1 := by {
            rw add_assoc,
            simp only [nat.add_sub_cancel_left],
          },
          rw ←this,
          rw finset.sum_Ico_eq_sum_range,
        }
    ... ≤ ∑ i in Ico ((χ $ 3 * k + 2) + 1) (n + m + 1), c i : by {
          apply @finset.sum_mono_set_of_nonneg ℕ ℝ _ _ c_nonneg,
          apply le_Ico_of_le_left _ h₆,
        }
    ... = ∑ i in Ico 0 (n + m + 1), c i - ∑ i in Ico 0 (χ (3 * k + 2) + 1), c i : by {
      have h₁' : ∑ i in Ico ((χ $ 3 * k + 2) + 1) (n + m + 1), c i + ∑ i in Ico 0 (χ (3 * k + 2) + 1), c i =  ∑ i in Ico 0 (n + m + 1), c i := by {
        have : Ico 0 (n + m + 1) \ Ico 0 (χ (3 * k + 2) + 1) = Ico (χ (3 * k + 2) + 1) (n + m + 1) := by apply finset.Ico.diff_left,
        rw ←this,
        apply finset.sum_sdiff,
        have h₂' : (χ (3 * k + 2)).succ ≤ n + m + 1 := by {
            have h₁'' : χ (3 * k + 2) + 1 ≤ n + 1 := add_le_add_right (le_trans (nat.le_succ _) h₆) 1,
            have h₂'' : n + 1 ≤ n + m + 1 := by {
              rw [add_comm n m, add_assoc],
              exact le_add_self,
            },
            exact le_trans h₁'' h₂'',
        },
        refine (finset.Ico.subset_iff (nat.succ_pos _)).mpr ⟨le_rfl, h₂'⟩,
      },
      exact eq_sub_of_add_eq h₁',
    }
    ... = ∑ i in range (n + m + 1), c i - ∑ i in range (χ (3 * k + 2) + 1), c i : by {
      repeat { rw finset.range_eq_Ico },
    }
    ... = ∑ i in range (χ (3 * k + 2) + r + 1), c i - ∑ i in range (χ (3 * k + 2) + 1), c i : by {
      have : n + m = χ (3 * k + 2) + r := by {
        -- simp [r],
        have : χ (3 * k + 2) ≤ n + m := by nlinarith,
        rw [←nat.add_sub_assoc this _],
        simp only [nat.add_sub_cancel_left],
      },
      rw this,
    }
    ... ≤ 1 / (↑(3 * k + 2) + 1) : by {
      specialize χ_cauchy_modulus_sum_c (3 * k + 2) (χ $ 3 * k + 2) r (le_refl _),
      rw real.dist_eq at χ_cauchy_modulus_sum_c,
      rw [abs_eq_self.mpr _] at χ_cauchy_modulus_sum_c,
      exact χ_cauchy_modulus_sum_c,
      dsimp only,
      rw [show χ (3 * k + 2) + r + 1 = χ (3 * k + 2) + 1 + r, by ring], 
      apply nonneg_sub_of_nonneg_sum c_nonneg,
    },

    calc s (n + m + 1)
        ≤ M * (∏ i in range (m + 1), (1 - (a $ n + i))) + (1 / (↑(3 * k + 2) + 1)) + ∑ i in range (m + 1), c (n + i) : h₅
    ... ≤ M * (∏ i in range (m + 1), (1 - (a $ n + i))) + (1 / (↑(3 * k + 2) + 1)) + 1 / (↑(3 * k + 2) + 1) : by nlinarith
    ... = ↑M * ∏ (i : ℕ) in range (m + 1), (1 - a (n + i)) + 2 / (↑(3 * k + 2) + 1) : by ring,
  end


  omit a_le_one
  include a_lt_one
  lemma leu_pin_3_5
  (M_pos : 0 < M)
  (s_le_M : ∀ n, s n ≤ M)
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
    have l_3_3 := leu_pin_3_3 a b c s M ψ χ a_nonneg (λ j, le_of_lt (a_lt_one j)) c_nonneg s_nonneg main_ineq M_pos s_le_M b_le_inv_k_succ χ_cauchy_modulus_sum_c k m (δ ψ χ k) (le_refl _),
    rw [real.dist_0_eq_abs, abs_of_nonneg (s_nonneg _)],
    have h₁ := finset.prod_range_add (1 - a) (δ ψ χ k) (m + 1),
    have h₂ : (∏ (x : ℕ) in range (δ ψ χ k + (m + 1)), (1 - a) x) / (∏ (x : ℕ) in range (δ ψ χ k), (1 - a) x) = (∏ (x : ℕ) in range (m + 1), (1 - a) (δ ψ χ k + x)) := by {
      refine (cancel_factors.cancel_factors_eq_div (eq.symm h₁) (ne.symm _)).symm,
      apply ne.symm,
      
      apply finset.prod_ne_zero_iff.mpr (λ i _, ne_of_gt $ _),
      work_on_goal 3 {
        simp only [pi.one_apply, pi.sub_apply],
        specialize a_lt_one i,
        exact sub_pos.mpr a_lt_one,
      },
      apply_instance, apply_instance,
    },

    have h₃ : n = δ ψ χ k + m + 1 := sorry,
     
    have h₄ : 1 / (∏ (x : ℕ) in range (δ ψ χ k), (1 - a) x) ≤ δ₀ k := sorry,

    have : ∏ i in range (δ ψ χ k + (m + 1)), (1 - a i) ≤ 1 / (3 * M * δ₀ k * (k + 1)) := sorry,

    have h₃ : ↑M * ∏ (i : ℕ) in range (m + 1), (1 - a (δ ψ χ k + i)) + 2 / (3 * ↑k + 2) ≤ 1 / (k + 1) :=
    calc ↑M * ∏ (i : ℕ) in range (m + 1), (1 - a (δ ψ χ k + i)) + 2 / (3 * ↑k + 2) 
        = ↑M * ((∏ (x : ℕ) in range (δ ψ χ k + (m + 1)), (1 - a) x) / ∏ (x : ℕ) in range (δ ψ χ k), (1 - a) x) + 2 / (3 * ↑k + 2) : by rw h₂; simp only [pi.one_apply, pi.sub_apply]
    ... = ↑M * ((∏ (x : ℕ) in range (δ ψ χ k + (m + 1)), (1 - a) x)) * (1 / ∏ (x : ℕ) in range (δ ψ χ k), (1 - a) x) + 2 / (3 * ↑k + 2) : by ring
    ... ≤ ↑M * ((∏ (x : ℕ) in range (δ ψ χ k + (m + 1)), (1 - a) x)) * δ₀ k + 2 / (3 * ↑k + 2) : by {
      have : 0 ≤ ↑M * ((∏ (x : ℕ) in range (δ ψ χ k + (m + 1)), (1 - a) x)) := sorry,
      nlinarith,
    }
    ... ≤ ↑M * (1 / (3 * M * δ₀ k * (k + 1))) * δ₀ k + 2 / (3 * ↑k + 2) : by {
      have : 0 ≤ (M : ℝ) := sorry,
      
    }
    ... ≤ 1 / (k + 1) : sorry

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

