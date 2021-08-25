import topology.metric_space.basic

variables {X : Type*} [metric_space X] 

open_locale big_operators 

def is_rate_of_convergence_towards (r : ℕ → ℕ) (x : ℕ → X) (L : X) : Prop :=
∀ k n : ℕ, r k ≤ n → (dist (x n) L ≤ 1 / ↑(k + 1))

def is_cauchy_modulus (r : ℕ → ℕ) (x : ℕ → X) : Prop :=
∀ k n p : ℕ, r k ≤ n → dist (x $ n + p) (x n) ≤ 1 / ↑(k + 1)

def is_rate_of_divergence (r : ℕ → ℕ) (x : ℕ → ℝ) : Prop :=
∀ n : ℕ, (n : ℝ) ≤ ∑ i in finset.range (r n + 1), x  i

def is_rate_of_asymptotic_regularity (r : ℕ → ℕ) (x : ℕ → X) : Prop :=
is_rate_of_convergence_towards r (λ i, dist (x $ i + 1) (x i)) 0

def is_rate_of_asymptotic_regularity_with_respect_to (r : ℕ → ℕ) (x : ℕ → X) (T : X → X) : Prop :=
is_rate_of_convergence_towards r (λ i, dist (T $ x i) (x i)) 0


