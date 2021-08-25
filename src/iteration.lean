import wspace 
import rates
import xu
import utils

open metric_space


local notation `|` x `|` := abs x

@[simp]
def tikhonov_mann {X : Type*} [whyperbolic_space X] (T : X → X) (o : X) (l β : ℕ → ℝ) (x₀ : X) : ℕ → X
| 0 := x₀
| (n + 1) := wmap (l n) (wmap (β n) o (tikhonov_mann n)) (T (wmap (β n) o (tikhonov_mann n)))


section 
  open whyperbolic_space

  -- using parameters for the hypotheses was a bad idea. 
  -- do not repeat

  parameters {X : Type*} [whyperbolic_space X] 
  parameters (T : X → X) (o : X) (l β : ℕ → ℝ) (x₀ : X) (p : X)
  parameters (Tne : ∀ s t : X, dist (T s) (T t) ≤ dist s t) (p_fp_T : T p = p) (h_p_neq_o : p ≠ o)
  parameters (l_pos : ∀ {n : ℕ}, 0 < l n) (hl1 : ∀ {n : ℕ}, l n ≤ 1)
  parameters (β_pos : ∀ {n : ℕ}, 0 < β n) (hβ1 : ∀ {n : ℕ}, β n ≤ 1)

  include Tne p_fp_T h_p_neq_o l_pos hl1 β_pos hβ1

  def x : ℕ → X := tikhonov_mann T o l β x₀
  def y (n : ℕ) : X := wmap (β n) o (x n)

  noncomputable def M := max (dist p x₀) (dist p o)


  lemma x_y : ∀ n : ℕ, x (n + 1) = wmap (l n) (y n) (T $ y n) := by intros n; induction n; simp [x, y]

  lemma hl0 : ∀ {n : ℕ}, 0 ≤ l n := λ _, le_of_lt l_pos

  lemma hβ0 : ∀ {n : ℕ}, 0 ≤ β n := λ _, le_of_lt β_pos

  lemma dist_p_o_pos : 0 < dist p o := 
  begin 
    refine (ne.le_iff_lt _).mp dist_nonneg,
    intros h,
    have : dist p o = 0 := h.symm,
    have := metric_space.eq_of_dist_eq_zero this,
    contradiction,
  end 

  lemma M_pos : 0 < M := lt_max_of_lt_right dist_p_o_pos

  lemma M_nonneg : 0 ≤ M := le_of_lt M_pos

  lemma M_double_nonneg : 0 ≤ 2 * M := mul_nonneg zero_le_two M_nonneg
  
  lemma left_le_M : dist p x₀ ≤ M := by simp [M]

  lemma right_le_M : dist p o ≤ M := by simp [M]



  -- # Corresponding to lemmas 3.1 and 3.2



  lemma l_3_1_i : ∀ n : ℕ, dist p (x $ n + 1)  ≤ (1 - (β n)) * (dist p o) + (β n) * (dist p (x n)) := 
  λ n, calc dist p (x $ n + 1) ≤ (1 - l n) * (dist p (y n)) + (l n) * (dist p (T $ y n)) : dist_conv _ _ _ hl0 hl1
    ... = (1 - l n) * (dist p (y n)) + (l n) * dist (T p) (T $ y n) : by rw p_fp_T
    ... ≤ (1 - l n) * (dist p (y n)) + (l n) * dist p (y n) : by {
      have := @hl0 n,
      have := @hl1 n,      
      nlinarith [Tne p (y n)],
    }
    ... = dist p (y n) : by { ring, }
    ... ≤ (1 - (β n)) * (dist p o) + (β n) * (dist p (x n)) : dist_conv _ _ _ hβ0 hβ1

  lemma l_3_1_ii_i : ∀ n : ℕ, dist p (x n) ≤ M := 
  begin   
    intros n,
    induction n,
    case zero
    { simp [M, x], },
    case succ: n ih {
      calc dist p (x $ n + 1) ≤ (1 - (β n)) * (dist p o) + (β n) * (dist p (x n)) : l_3_1_i n
      ... ≤ (1 - (β n)) * M + (β n) * (dist p (x n)) : by {
        have : dist p o ≤ M := by simp [M],
        nlinarith [@hβ0 n, @hβ1 n],
      }
      ... ≤ (1 - (β n)) * M + (β n) * M : by { nlinarith [@hβ0 n, @hβ1 n, ih], }
      ... ≤ M : by ring,
    }
  end 

  lemma l_3_1_ii_ii : ∀ n : ℕ, dist (x n) o ≤ 2 * M :=
  λ n, calc dist (x n) o ≤ dist (x n) p + dist p o : dist_triangle _ _ _
  ... ≤ M + dist p o : by{
    nth_rewrite 0 dist_comm,
    linarith [l_3_1_ii_i n],
  }
  ... ≤ M + M : by {have : dist p o ≤ M := by simp [M], linarith, }
  ... = 2 * M : by ring

  lemma l_3_1_iii_i : ∀ n : ℕ, dist p (y n) ≤ M := 
  λ n, calc 
  dist p (y n) ≤ (1 - β n) * (dist p o) + (β n) * (dist p (x n)) : dist_conv _ _ _ hβ0 hβ1
  ... ≤ (1 - β n) * M + (β n) * (dist p (x n)) : by nlinarith [right_le_M, @hβ0 n, @hβ1 n]
  ... ≤ (1 - β n) * M + (β n) * M : by nlinarith [@hβ0 n, @hβ1 n, @l_3_1_ii_i n]
  ... = M : by ring

  lemma l_3_1_iii_ii : ∀ n : ℕ, dist (y n) (T $ y n) ≤ 2 * M :=
  λ n, calc 
  dist (y n) (T $ y n) ≤ dist (y n) p + dist p (T $ y n) : dist_triangle _ _ _
  ... = dist (y n) p + dist (T p) (T $ y n) : by rw p_fp_T
  ... ≤ dist (y n) p + dist p (y n) : by nlinarith [Tne p (y n)]
  ... = dist p (y n) + dist p (y n) : by rw dist_comm 
  ... ≤ M + M : by nlinarith [l_3_1_iii_i n]
  ... = 2 * M : by ring


  lemma l_3_2_i : ∀ n : ℕ, 
  dist (y $ n + 1) (y n)  ≤ (β $ n + 1) * (dist (x $ n + 1) (x n)) + 2 * M * |(β $ n + 1) - β n| := 
  λ n, calc 
  dist (y $ n + 1) (y n)  ≤ (β $ n + 1) * (dist (x $ n + 1) (x n)) + |(β $ n + 1) - β n| * (dist o (x n)) : @dist_wmap_same_first _ _ _ _ o (x $ n + 1)(x n) (@hβ0 $ n + 1) (@hβ1 $ n + 1) (@hβ0 n) (@hβ1 n)
  ... ≤ (β $ n + 1) * (dist (x $ n + 1) (x n)) + |(β $ n + 1) - β n| * (2 * M) : by {
    nth_rewrite 1 dist_comm,
    nlinarith [M_pos, l_3_1_ii_ii n, abs_nonneg (β (n + 1) - β n)],
  }
  ... = (β $ n + 1) * (dist (x $ n + 1) (x n)) + 2 * M * |(β $ n + 1) - β n| : by ring

  lemma l_3_2_ii : 
  ∀ n : ℕ, dist (x $ n + 2) (x $ n + 1) 
  ≤ (β $ n + 1) * (dist (x $ n + 1) (x n)) + 2 * M * (|(β $ n + 1) - β n| + |(l $ n + 1) - l n|) := 
  λ n, calc 
  dist (x $ n + 2) (x $ n + 1) = dist (wmap (l $ n + 1) (y $ n + 1) (T $ y $ n + 1)) (wmap (l n) (y n) (T $ y n)) : by simp [x_y]
  ... ≤ (1 - l (n + 1)) * (dist (y $ n + 1) (y n)) + (l $ n + 1) * (dist (T $ y $ n + 1) (T $ y $ n)) 
      + |l (n + 1) - l n| * (dist (y n) (T $ y $ n)) : dist_wmap hl0 hl1 hl0 hl1
  ... ≤ (1 - l (n + 1)) * (dist (y $ n + 1) (y n)) + (l $ n + 1) * (dist (y $ n + 1) (y n)) 
      + |l (n + 1) - l n| * (dist (y n) (T $ y $ n)) : by nlinarith [Tne (y $ n + 1) (y n), @hl0 (n + 1)]
  ... = dist (y $ n + 1) (y n) + |l (n + 1) - l n| * (dist (y n) (T $ y n)) : by ring
  ... ≤ dist (y $ n + 1) (y n) + |l (n + 1) - l n| * (2 * M) : by nlinarith [l_3_1_iii_ii n, abs_nonneg (l (n + 1) - l n)]
  ... ≤ (β $ n + 1) * (dist (x $ n + 1) (x n)) + 2 * M * |(β $ n + 1) - β n| + |l (n + 1) - l n| * (2 * M) : by nlinarith [l_3_2_i n, abs_nonneg (l (n + 1) - l n)]
  ... = (β $ n + 1) * (dist (x $ n + 1) (x n)) + 2 * M * (|(β $ n + 1) - β n| + |(l $ n + 1) - l n|) : by ring

  lemma l_3_2_iii : 
  ∀ n : ℕ, dist (x n) (y n) = (1 - β n) * (dist o (x n)) :=
  begin 
    intros n,
    have h₁ := @hβ0 n,
    have h₂ := @hβ1 n,
    simp only [y],
    rw [dist_self_wmap_right h₁ h₂],
  end

  lemma l_3_2_iv : 
  ∀ n : ℕ, dist (x n) (T $ x n) ≤ dist (x n) (x $ n + 1) + (l n) * (1 - β n) * (dist o (x n)) +
  (1 - l n) * (β n) * (dist (x n) (T $ x n)) +
  (1 - l n) * (1 - β n) * (dist o (T $ x n)) :=
  λ n, calc 
  dist (x n) (T $ x n) 
      ≤ dist (x n) (x $ n + 1) + dist (x $ n + 1) (T $ x n) : dist_triangle _ _ _ 
  ... = dist (x n) (x $ n + 1) + dist (wmap (l n) (y n) (T $ y n)) (T $ x n) : by simp [x_y]
  ... = dist (x n) (x $ n + 1) + dist (T $ x n) (wmap (l n) (y n) (T $ y n)) : by nth_rewrite 1 dist_comm
  ... ≤ (dist (x n) (x $ n + 1)) + (1 - l n) * (dist (y n) (T $ x n)) + (l n) * (dist (T $ y n) (T $ x n)) : by{
    rw [dist_comm (y n) (T $ x n), dist_comm (T $ y n) (T $ x n)],
    nlinarith [dist_conv (y n) (T $ y n) (T $ x n) (@hl0 n) (@hl1 n)],
  }
  ... ≤ (dist (x n) (x $ n + 1)) + (1 - l n) * (dist (y n) (T $ x n)) + (l n) * (dist (y n) (x n)) : by nlinarith [Tne (y n) (x n), @hl0 n]
  ... ≤ (dist (x n) (x $ n + 1)) + (l n) * (dist (y n) (x n)) + (1 - l n) * (dist (y n) (T $ x n)) : by ring
  ... ≤ (dist (x n) (x $ n + 1)) + (l n) * (dist (y n) (x n)) 
        + (1 - l n) * (dist (y n) (wmap (β n) o (T $ x n)) + dist (wmap (β n) o (T $ x n)) (T $ x n)) : by nlinarith [dist_triangle (y n) (wmap (β n) o (T $ x n)) (T $ x n), @hl0 n, sub_nonneg.mpr (@hl1 n)]
  ... = (dist (x n) (x $ n + 1)) + (l n) * (dist (y n) (x n)) 
        + (1 - l n) * (dist (y n) (wmap (β n) o (T $ x n))) + (1 - l n) * (dist (wmap (β n) o (T $ x n)) (T $ x n)) : by ring 
  ... = (dist (x n) (x $ n + 1)) + (l n) * (dist (y n) (x n)) 
        + (1 - l n) * (dist (y n) (wmap (β n) o (T $ x n))) 
        + (1 - l n) * (1 - β n) * (dist o (T $ x n)) : by { rw [dist_comm (wmap (β n) o (T $ x n)) (T $ x n), dist_self_wmap_right hβ0 hβ1], ring, }
  ... = (dist (x n) (x $ n + 1)) + (l n) * (dist (y n) (x n)) + (1 - l n) * (1 - β n) * (dist o (T $ x n)) 
        +  (1 - l n) * (dist (y n) (wmap (β n) o (T $ x n))) : by ring
  ... = (dist (x n) (x $ n + 1)) + (l n) * (dist (y n) (x n)) + (1 - l n) * (1 - β n) * (dist o (T $ x n)) 
        + (1 - l n) * (dist (wmap (β n) o (x n)) (wmap (β n) o (T $ x n))) : by simp [y]
  ... = (dist (x n) (x $ n + 1)) + (l n) * (1 - β n) * (dist o (x n)) + (1 - l n) * (1 - β n) * (dist o (T $ x n)) 
        + (1 - l n) * (dist (wmap (β n) o (x n)) (wmap (β n) o (T $ x n))) : by {
          rw [dist_comm (y n) (x n)],
          have : dist (x n) (y n) = (1 - β n) * dist o (x n) := l_3_2_iii n,
          simp only [*, add_left_inj, add_right_inj],
          ring,
        }
  ... ≤ (dist (x n) (x $ n + 1)) + (l n) * (1 - β n) * (dist o (x n)) + (1 - l n) * (1 - β n) * (dist o (T $ x n)) 
        + (1 - l n) * (β n) * (dist (x n) (T $ x n)) : by nlinarith [sub_nonneg.mpr (@hl1 n), @wmap_same_coeff_same_firt _ _ _ o (x n) (T $ x n) (@hβ0 n) (@hβ1 n)]
  ... = dist (x n) (x $ n + 1) + (l n) * (1 - β n) * (dist o (x n)) + 
  (1 - l n) * (β n) * (dist (x n) (T $ x n)) +
  (1 - l n) * (1 - β n) * (dist o (T $ x n)) : by ring

  lemma l_3_2_v : ∀ n : ℕ,
  (l n) * (dist (x n) (T $ x n)) ≤ dist (x n) (x $ n + 1) + 2 * M * (1 - β n) :=
  λ n, begin 
    have h₁ : dist (x n) (T $ x n) ≤ dist (x n) (x $ n + 1) + (1 - β n) * (2 * M) + (1 - l n) * (dist (x n) (T $ x n)),
    calc 
    dist (x n) (T $ x n) 
        ≤ dist (x n) (x $ n + 1) + (l n) * (1 - β n) * (dist o (x n)) + (1 - l n) * (β n) * (dist (x n) (T $ x n)) 
          + (1 - l n) * (1 - β n) * (dist o (T $ x n)) : by apply l_3_2_iv
    ... ≤ dist (x n) (x $ n + 1) + (l n) * (1 - β n) * (dist o (x n)) + (1 - l n) * (β n) * (dist (x n) (T $ x n)) 
          + (1 - l n) * (1 - β n) * ((dist o (x n)) +  (dist (x n) (T $ x n))) : by nlinarith [mul_nonneg (sub_nonneg.mpr $ @hl1 n) (sub_nonneg.mpr $ @hβ1 n), dist_triangle o (x n) (T $ x n)]
    ... = dist (x n) (x $ n + 1) + (l n) * (1 - β n) * (dist o (x n)) + (1 - l n) * (β n) * (dist (x n) (T $ x n)) 
          + (1 - l n) * (1 - β n) * (dist o (x n)) + (1 - l n) * (1 - β n) * (dist (x n) (T $ x n)) : by ring
    ... ≤ dist (x n) (x $ n + 1) + (1 - β n) * (dist o (x n)) + (1 - l n) * (dist (x n) (T $ x n)) : by ring
    ... ≤ dist (x n) (x $ n + 1) + (1 - β n) * (2 * M) + (1 - l n) * (dist (x n) (T $ x n)) : by { rw [dist_comm o (x n)], nlinarith [sub_nonneg.mpr (@hβ1 n), l_3_1_ii_ii n], },

    have h₂ : dist (x n) (T $ x n) - (1 - l n) * (dist (x n) (T $ x n)) ≤ dist (x n) (x $ n + 1) + (1 - β n) * (2 * M) := sub_le_iff_le_add.mpr h₁,
    have h₃ : dist (x n) (T $ x n) - (1 - l n) * (dist (x n) (T $ x n)) = (l n) * (dist (x n) (T $ x n)) := by ring,
    rw [h₃, mul_comm (1 - β n) (2 * M)] at h₂,
    exact h₂,
  end





  -- # Main results
  
  parameters {σ₂ σ₃ σ₄ σ₅ : ℕ → ℕ} {Λ NΛ : ℕ} (Λ_pos : 0 < Λ)
  include Λ_pos

  open_locale big_operators

  open finset (range)

  def cond₂ : Prop := is_rate_of_convergence_towards σ₂ (λ n, ∏ i in range (n + 1), (β $ i + 1)) 0

  def cond₃ : Prop := is_cauchy_modulus σ₃ (λ n, ∑ i in range (n + 1), |β (i + 1) - β i|)

  def cond₄ : Prop := is_cauchy_modulus σ₄ (λ n, ∑ i in range (n + 1), |l (i + 1) - l i|)

  def cond₅ : Prop := is_rate_of_convergence_towards σ₅ β 1

  def cond₆ : Prop := ∀ n : ℕ, NΛ ≤ n → 1 / (Λ : ℝ) ≤ l n

  parameters (K : ℕ) (h_M_le_K : (M : ℝ) ≤ (K : ℝ)) (ψ : ℕ → ℕ) (hψ_pos : ∀ k : ℕ, 0 < ψ k)
  include h_M_le_K

  def L := 2 * K 
  def s (n : ℕ) : ℝ := dist (x $ n + 1) (x n)
  def a (n : ℕ) : ℝ := 1 - (β $ n + 1)
  def P (n : ℕ) : ℝ := ∏ i in range (n + 1), (1 - a i)
  noncomputable def c (n : ℕ) : ℝ := 2 * M * (|β (n + 1) - (β n)| + |l (n + 1) - l n|)
  noncomputable def c' (n : ℕ) : ℝ := ∑ i in range (n + 1), c i

  lemma a_pos : ∀ {n : ℕ}, 0 ≤ a n := 
  by { intros n, simp only [a, sub_nonneg], exact hβ1, }

  lemma one_sub_a_nonneg : ∀ {n : ℕ}, 0 ≤ (1 - a n) :=
  by { intros n, simp only [a, sub_sub_cancel], exact hβ0, }

  lemma a_lt_one : ∀ {n : ℕ}, a n < 1 := 
  by { intros n, simp only [a, sub_lt_self_iff], exact β_pos, }

  lemma c_pos : ∀ {n : ℕ}, 0 ≤ c n := 
  begin
    intros n,
    simp only [c],
    exact mul_nonneg (mul_nonneg zero_le_two M_nonneg) (add_nonneg (abs_nonneg _) (abs_nonneg _)),
  end

  lemma s_pos : ∀ {n : ℕ}, 0 ≤ s n := 
  begin 
    intros n,
    simp only [s],
    exact dist_nonneg,
  end

  lemma P_pos : ∀ {n : ℕ}, 0 ≤ (P n) := 
  begin 
    intros n,
    simp only [P],
    exact finset.prod_nonneg (λ i _, one_sub_a_nonneg),
  end

  lemma xu_ineq_s_a_c : ∀ {n : ℕ}, s (n + 1) ≤ (1 - a n) * s n + c n := 
  begin 
    intros n,
    simp only [s, a, c, sub_sub_cancel],
    have : n + 1 + 1 = n + 2 := by ring,
    rw this,
    exact l_3_2_ii n,
  end

  lemma s_le_L : ∀ {n : ℕ}, s n ≤ (L : ℝ) := 
  begin 
    simp only [L, s, nat.cast_bit0, nat.cast_one, nat.cast_mul],
    intros n,
    calc dist (x $ n + 1) (x n) ≤ dist (x $ n + 1) p + dist p (x n) : dist_triangle _ _ _ 
    ... = dist p (x $ n + 1) + dist p (x n) : by rw dist_comm 
    ... ≤ M + M : add_le_add (l_3_1_ii_i _) (l_3_1_ii_i _)
    ... ≤ K + K : add_le_add h_M_le_K h_M_le_K
    ... = 2 * K : by ring,
  end
   
  set_option pp.all false
  lemma σ₂_rate_conv_P : cond₂ → is_rate_of_convergence_towards σ₂ P 0 := 
  begin 
    intros hc₂,
    intros k n h,
    rw [real.dist_eq, sub_zero, abs_eq_self.mpr P_pos],
    simp only [P, a, one_div, sub_sub_cancel, nat.cast_add, nat.cast_one],
    dunfold cond₂ at hc₂,
    specialize hc₂ k n h,
    dsimp only at hc₂,
    have : 0 ≤ ∏ i in range (n + 1), β (i + 1) := finset.prod_nonneg (λ i _, hβ0),
    rw [real.dist_eq, sub_zero, abs_eq_self.mpr this] at hc₂,
    clear this,
    ring_nf at hc₂,
    simp only [nat.cast_add, nat.cast_one] at hc₂,
    exact hc₂,
  end

  lemma L_def : L = 2 * K := rfl

  lemma K_pos : 0 < K := (@nat.cast_pos ℝ _ _ K).mp (lt_of_lt_of_le M_pos h_M_le_K)

  lemma M_le_L : M ≤ L := 
  begin 
    simp only [L, nat.cast_bit0, nat.cast_one, nat.cast_mul],
    nlinarith [M_pos],
  end


  lemma L_pos : 0 < L := nat.succ_mul_pos 1 K_pos

  lemma L_pos_real : (0 : ℝ) < L := nat.cast_pos.mpr L_pos

  def χ (k : ℕ) : ℕ := 
  max 
    (σ₃ $ 8 * K * (k + 1) - 1)
    (σ₄ $ 8 * K * (k + 1) - 1)
  
  def Ω (k : ℕ) : ℕ := 
  max 
    (σ₂ $ 6 * K * (k + 1) * (ψ k) - 1)
    (χ (3 * k + 2) + 1)
    + 1

  def Φ (k : ℕ) : ℕ := (max3 NΛ (Ω $ 2 * Λ * (k + 1) - 1) (σ₅ $ 4 * K * Λ * (k + 1) - 1)) + 1

  def Γ (φ : ℕ → ℕ) (k : ℕ) : ℕ := (max3 NΛ (φ $ 2 * Λ * (k + 1) - 1) (σ₅ $ 4 * K * Λ * (k + 1) - 1)) + 1  

  parameter (hψ : ∀ k : ℕ, 1 / (ψ k : ℝ) ≤ P (χ $ 3 * k + 2))

  -- set_option pp.all true
  lemma l_5_3 (hc₃ : cond₃) (hc₄ : cond₄) : is_cauchy_modulus χ c' := 
  begin 

    intros k n j h,
    have hσ₃_le_n : σ₃ (8 * K * (k + 1) - 1) ≤ n := le_of_max_le_left h,
    have hσ₄_le_n : σ₄ (8 * K * (k + 1) - 1) ≤ n := le_of_max_le_right h,
    have hc₃' := hc₃ _ _ j hσ₃_le_n,
    have hc₄' := hc₄ _ _ j hσ₄_le_n,
    set β' : ℕ → ℝ := λ n, ∑ i in range (n + 1), |β (i + 1) - β i|,
    set l' : ℕ → ℝ := λ n, ∑ i in range (n + 1), |l (i + 1) - l i|,
    rw [real.dist_eq] at hc₃' hc₄',
    have : 8 * K = 4 * L := by { dsimp only [L], ring, },
    rw this at *, clear this,
    have h_4LK_pos : 0 < 4 * L * (k + 1) := mul_pos (mul_pos zero_lt_four L_pos) (nat.succ_pos k),
    have : 4 * L * (k + 1) - 1 + 1 = 4 * L * (k + 1) := nat.succ_pred_eq_of_pos h_4LK_pos,
    rw this at *, clear this,

    have h_c_β_l : ∀ m : ℕ, c' m = 2 * M * (β' m + l' m) := 
    begin
      intros m,
      simp only [c', c, β', l'],
      rw [finset.sum_hom, finset.sum_add_distrib],
    end,

    have h_β'_sub_abs : |β' (n + j) - β' n| = β' (n + j) - β' n := by {
      apply abs_eq_self.mpr,
      dsimp only [β'],
      have : n + j + 1 = (n + 1) + j := by ring,
      rw this,
      apply nonneg_sub_of_nonneg_sum,
      intros, 
      apply abs_nonneg,
    },
    have h_l'_sub_abs : |l' (n + j) - l' n| = l' (n + j) - l' n := by {
      apply abs_eq_self.mpr,
      dsimp only [l'],
      have : n + j + 1 = (n + 1) + j := by ring,
      rw this,
      apply nonneg_sub_of_nonneg_sum,
      intros, 
      apply abs_nonneg,
    },
    rw h_β'_sub_abs at hc₃',
    rw h_l'_sub_abs at hc₄',

    have h_2M_pos : 0 < 2 * M := mul_pos zero_lt_two M_pos,

    have h_c'_le : c' (n + j) - c' n ≤ 1 / ↑(k + 1) :=
    calc c' (n + j) - c' n 
        = 2 * M * (β' (n + j) + l' (n + j)) - 2 * M * (β' n + l' n) : by repeat { rw [h_c_β_l] }
    ... = 2 * M * ((β' (n + j) - β' n) + (l' (n + j) - l' n)) : by ring
    ... ≤ 2 * M * (1 / ↑(4 * L * (k + 1)) + 1 / ↑(4 * L * (k + 1))) : by nlinarith
    ... = 2 * M * (2 / ↑(4 * L * (k + 1))) : by ring
    ... = 2 * M * (2 / (4 * ↑L * (↑k + 1))) : by simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul]
    ... = 4 * M / (4 * ↑L * (↑k + 1)) : by ring
    ... = 4 * M / (4 * (↑L * (↑k + 1))) : by rw mul_assoc
    ... = M / (↑L * (↑k + 1)) : mul_div_mul_left _ _ (by norm_num)
    ... = (M / ↑L) * (1 / (↑k + 1)) : by { ring_nf, rw [mul_inv', mul_comm (↑L)⁻¹ _], }
    ... ≤ 1 * (1 / ↑(k + 1)) : by {
      -- have : (0 : ℝ) < ↑L := L_pos_real,
      have h_M_div_L_le_one : (M / (L : ℝ)) ≤ 1 := (@div_le_one ℝ _ M ↑L L_pos_real).mpr M_le_L,
      have h_one_div_k_succ_pos : (0 : ℝ) < 1 / ↑(k + 1) := one_div_pos.mpr (nat.cast_pos.mpr $ nat.succ_pos k),
      exact (mul_le_mul_right h_one_div_k_succ_pos).mpr h_M_div_L_le_one,
    }
    ... = 1 / ↑(k + 1) : one_mul _,

    have h_c'_sub_abs : |c' (n + j) - c' n| = c' (n + j) - c' n := by {
      apply abs_eq_self.mpr,
      dsimp only [c'],
      have : n + j + 1 = (n + 1) + j := by ring,
      rw this, clear this,
      apply nonneg_sub_of_nonneg_sum,
      intros, 
      have : 0 ≤ |β (i + 1) - β i| + |l (i + 1) - l i| := add_nonneg (abs_nonneg _) (abs_nonneg _),
      nlinarith,
    },
    rw [real.dist_eq, h_c'_sub_abs],
    exact h_c'_le,
  end

  lemma Λ_pos_real : 0 < (Λ : ℝ) := nat.cast_pos.mpr Λ_pos

  lemma add_div_two_self (a : ℝ)  (h : a ≠ 0) : 1 / (2 * a) + 1 / (2 * a) = 1 / a := 
  calc 1 / (2 * a) + 1 / (2 * a) 
      = (2 / (2 * a)) : by ring
  ... = (1 / a) : by rw [div_mul_right a two_ne_zero]

  lemma β_sub_one_neg : ∀ {n : ℕ}, β n - 1 ≤ 0 := λ n, by nlinarith [@hβ1 n] 

  lemma l_5_5 (hc₅ : cond₅) (hc₆ : cond₆) (Θ : ℕ → ℕ) (Θar : is_rate_of_asymptotic_regularity Θ x) :
  is_rate_of_asymptotic_regularity_with_respect_to (Γ Θ) x T :=
  begin 
    intros k n h,
    dsimp only at ⊢,
    rw [real.dist_eq, sub_zero, abs_eq_self.mpr dist_nonneg],
    have h_le₁ : NΛ ≤ n := le_trans (le_trans max3_le₁ (nat.le_succ _)) h,
    have h_le₂ : Θ (2 * Λ * (k + 1) - 1) ≤ n := le_trans (le_trans max3_le₂ (nat.le_succ _)) h,
    have h_le₃ : σ₅ (4 * K * Λ * (k + 1) - 1) ≤ n := le_trans (le_trans max3_le₃ (nat.le_succ _)) h,

    dunfold cond₅ at hc₅,
    dunfold cond₆ at hc₆,

    have k_succ_pos_real : 0 < (k : ℝ) + 1 := nat.cast_add_one_pos k,

    have hΛ : 1 / (l n) ≤ Λ := by {
      have h'₂ : 0 < l n := l_pos,
      have := hc₆ n h_le₁,
      refine (one_div_le l_pos Λ_pos_real).mpr this,
    },
    have h₁ : dist (T $ x n) (x n) ≤ Λ * (dist (x n) (x $ n + 1) + 2 * M * (1 - β n)) := by {
      have p₁ := l_3_2_v n,
      have p₂ : dist (x n) (T $ x n) ≤ (1 / l n) * (dist (x n) (x (n + 1)) + 2 * M * (1 - β n)) := by {
        apply helper,
        exact p₁,
      },
      rw dist_comm at p₂,
      have p₃ : (1 / l n) * (dist (x n) (x (n + 1)) + 2 * M * (1 - β n)) ≤ ↑Λ * (dist (x n) (x (n + 1)) + 2 * M * (1 - β n)) := 
        mul_mono_nonneg (add_nonneg dist_nonneg (by nlinarith [M_pos, @β_pos n, @hβ1 n])) hΛ,
      refine le_trans p₂ p₃,
    },

    have h₂ : dist (x n) (x $ n + 1) ≤ 1 / (2 * Λ * (k + 1)) := by {
      specialize Θar (2 * Λ * (k + 1) - 1) n h_le₂,
      dsimp only at Θar,
      rw [real.dist_eq, sub_zero, abs_eq_self.mpr dist_nonneg] at Θar,
      rw dist_comm at Θar,
      have h_2ΛK_pos : 0 < 2 * Λ * (k + 1) := by nlinarith,
      have : 2 * Λ * (k + 1) - 1 + 1 = 2 * Λ * (k + 1) := nat.succ_pred_eq_of_pos h_2ΛK_pos,
      rw this at Θar,
      simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul] at Θar,
      exact Θar,
    },

    have h₃ : 2 * M * (1 - β n) ≤ 1 / (2 * Λ * (k + 1)) := by {
      specialize hc₅ ((4 * K * Λ * (k + 1) - 1)) n h_le₃,
      rw [real.dist_eq, abs_of_nonpos β_sub_one_neg, neg_sub] at hc₅,
      have h_4KK_pos : 0 < 4 * K * Λ * (k + 1) := by repeat { apply mul_pos }; try { nlinarith [K_pos] },
      have : 4 * K * Λ * (k + 1) - 1 + 1 = 4 * K * Λ * (k + 1) := nat.succ_pred_eq_of_pos h_4KK_pos,
      rw this at hc₅, clear this,
      have := mul_sides_left _ _ (2 * M) _ _ hc₅, -- this is awful
      all_goals { sorry },
    },

    calc dist (T $ x n) (x n) 
        ≤ Λ * (dist (x n) (x $ n + 1) + 2 * M * (1 - β n)) : h₁
    ... ≤ Λ * ((1 / (2 * Λ * (k + 1))) + 2 * M * (1 - β n)) : (mul_le_mul_left Λ_pos_real).mpr (add_le_add_right h₂ _)
    ... = Λ * (1 / (2 * Λ * (k + 1))) + Λ * 2 * M * (1 - β n) : by ring
    ... = Λ / (2 * Λ * (k + 1)) + Λ * (2 * M * (1 - β n)) : by ring
    ... = Λ / (Λ * 2 * (k + 1)) + Λ * (2 * M * (1 - β n)) : by rw [mul_comm 2 (Λ : ℝ)]
    ... = 1 / (2 * (k + 1)) + Λ * (2 * M * (1 - β n)) : by {
      have : (Λ : ℝ) / ((Λ : ℝ) * 2 * (↑k + 1)) = 1 / (2 * (k + 1)) := by {
        rw [mul_assoc (Λ : ℝ) 2 (k + 1)],
        exact div_mul_right _ (ne_of_gt Λ_pos_real),
      },
      rw this,
    }
    ... ≤ 1 / (2 * (k + 1)) + Λ * (1 / (2 * Λ * (k + 1))) : add_le_add_left ((mul_le_mul_left Λ_pos_real).mpr h₃) _
    ... = 1 / (2 * (k + 1)) + Λ * (1 / (Λ * (2 * (k + 1)))) : by rw [mul_comm 2 (Λ : ℝ), mul_assoc (Λ : ℝ) 2 (k + 1)]
    ... = 1 / (2 * (k + 1)) + Λ / (Λ * (2 * (k + 1))) : by ring
    ... = 1 / (2 * (k + 1)) + 1 / (2 * (k + 1)) : by  rw [div_mul_right _ (ne_of_gt Λ_pos_real)]
    ... = 1 / (↑k + 1) :  add_div_two_self _ (ne_of_gt k_succ_pos_real),
  
  end
  
  include hψ
  theorem main₁ 
  (hc₂ : cond₂)
  (hc₃ : cond₃)
  (hc₄ : cond₄)
  : is_rate_of_asymptotic_regularity Ω x := 
  begin 
    have xu := xu_quantitative a c s L χ σ₂ ψ @a_pos @a_lt_one @c_pos @s_pos L_pos @xu_ineq_s_a_c @s_le_L (l_5_3 hc₃ hc₄) (σ₂_rate_conv_P hc₂) hψ,
    dsimp only [is_rate_of_asymptotic_regularity],
    have : s = λ (i : ℕ), dist (x (i + 1)) (x i) := by refl,
    rw ←this, clear this,
    have : Ω = xu_rate χ σ₂ ψ L := by {
      ext,
      simp [Ω, xu_rate, L],
      ring,
    },
    rw this,
    exact xu,
  end
  
  theorem main₂ 
  (hc₂ : cond₂)
  (hc₃ : cond₃)
  (hc₄ : cond₄)
  (hc₅ : cond₅)
  (hc₆ : cond₆)
  : is_rate_of_asymptotic_regularity_with_respect_to Φ x T :=
  begin 
    have : Φ = Γ Ω := by {
      ext,
      
      simp [Φ, Γ, Ω],
    },
    rw this,
    exact l_5_5 hc₅ hc₆ Ω (main₁ hc₂ hc₃ hc₄),
  end
end

#check finset.sum_add_distrib
open_locale big_operators 
#check finset.sum_hom
example (a b : ℕ → ℝ) (c : ℝ) (n : ℕ) : ∑ i in finset.range n, c * a i = c * (∑ i in finset.range n, a i) := 
begin 
  exact (finset.range n).sum_hom (has_mul.mul c),
end
#check div_le_one

example (a : ℝ) (h : 0 < a) : 0 < (1 / a) := by {
  exact one_div_pos.mpr h,
}

example (k : ℕ) : (0 : ℝ) < (k.succ) := by {
  have : (0 : ℕ) < k.succ := nat.succ_pos k,
  exact nat.cast_pos.mpr (nat.succ_pos k),
}

example (a b : ℝ) (h : a ≤ b) (h₁ : 0 < a) (h₂ : 0 < b) : (a / b ≤ 1) :=
by {
  exact (div_le_one h₂).mpr h,
}
/-
Try this: exact gt_of_ge_of_gt h₂ h₁
-/

example (a b : ℝ) (h : 1 / a ≤ b) (h₁ : 0 < a) (h₂ : 0 < b) : 1 / b ≤ a := by {
  exact (one_div_le h₁ h₂).mp h,
}

example (a b c : ℝ) (h : b ≤ c) (h₁ : 0 < a) : a * b ≤ a * c := by {
  exact (mul_le_mul_left h₁).mpr h,
}

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by {
  exact add_le_add_right h c,
}

example (a b : ℝ) (h₁: 0 < a) (h₂ : 0 < b) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by {
  exact mul_inv_rev' a b,
}
example (a : ℝ) (h : 0 < a) : a * a⁻¹ = 1 := by {
}

example (a b : ℝ) (h₁ : 0 ≠ a) (h₂ : 0 ≠ b) : a / (a * b) = 1 / b := by {
  exact div_mul_right b (ne.symm h₁),
  -- ring_nf,
  -- rw [mul_inv_rev', mul_assoc, inv_mul_cancel (ne_of_gt h₁), mul_one],
}

example (a : ℝ) : a + a = 2 * a := by {
  ring,
}
 
example (a : ℝ)  (h : a ≠ 0) : 1 / (2 * a) + 1 / (2 * a) = 1 / a := 
calc 1 / (2 * a) + 1 / (2 * a) 
    = (2 / (2 * a)) : by ring
... = (1 / a) : by rw [div_mul_right a two_ne_zero]

example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) 
: a * b ≤ c → b ≤ a⁻¹ * c := by {
  have : a * b ≤ c → a⁻¹ * (a * b) ≤ a⁻¹ * c := (mul_le_mul_left (inv_pos.mpr ha)).mpr,
  rw [←mul_assoc, inv_mul_cancel (ne_of_gt ha), one_mul] at this,
  exact this,
}

example (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : b ≤ c → a * b ≤ a * c := by {
  exact (mul_le_mul_left ha).mpr,
}

example (a b c : ℝ) (h' : b ≤ c) (h : 0 ≤ a) : b * a ≤ c * a := by {
  exact mul_mono_nonneg h h',
}


#check (mul_le_mul_left _).mpr

example (a b : ℝ) : - (a - b) = b -a := neg_sub a b

example (a : ℝ) (h : a ≤ 0) : abs a = -a := abs_of_nonpos h

example (s : finset ℕ) (x : ℕ) (h : x ∈ s) : x ≤ s.sup id := by {
  have := @finset.le_sup _ _ _ _ id _ h,
  exact this,
} 

example (a : ℕ) : a ≤ a + 1 := nat.le_succ a



#check finset.prod_nonneg
#check finset.sum_nonneg

example (a b c d : ℝ) (h₁ : 0 ≠ a) (h₂ : 0 ≠ c) : (a * b) / (a * c) = b / c := by {
  exact mul_div_mul_left b c (ne.symm h₁),
}

