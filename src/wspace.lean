import data.real.basic
import topology.metric_space.basic
import tactic

class has_wmap (α : Type*) :=
(wmap : ℝ → α → α → α)

export has_wmap (wmap)

instance : has_wmap ℝ :=
⟨λ a x y, (1 - a) * x + a * y⟩

class whyperbolic_space (X : Type*) extends has_wmap X, metric_space X :=
(dist_conv : ∀ {a : ℝ} (x y z : X), 0 ≤ a → a ≤ 1 → 
  dist z (wmap a x y) ≤ (1 - a) * (dist z x) + a * (dist z y))
(same_points : ∀ {a b : ℝ} (x y : X), 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
  dist (wmap a x y) (wmap b x y) = (abs $ a - b) * (dist x y))
(w_antisymm : ∀ {a : ℝ} (x y : X), 0 ≤ a → a ≤ 1 →
  wmap a x y = wmap (1 - a) y x)
(same_coeff : ∀ {a : ℝ} (x y z w : X),  0 ≤ a → a ≤ 1 →
  dist (wmap a x z) (wmap a y w) ≤ (1 - a) * (dist x y) + a * (dist z w))

namespace whyperbolic_space


-- def convex (C : set X) : Prop := ∀ x y : X, x ∈ C → y ∈ C → ∀ a : ℝ, 0 ≤ a → a ≤ 1 → wmap a x y ∈ C

section basic_lemmas


  variables {X : Type*} [whyperbolic_space X] 
  variables {a b : ℝ} {x y z w : X}  (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) 


  include ha0 ha1 

    lemma dist_self_wmap : dist x (wmap a x y) = a * (dist x y) ∧ dist y (wmap a x y) = (1 - a) * (dist x y) :=
    begin 
      have hx := @whyperbolic_space.dist_conv _ _ _ x y x ha0 ha1,
      have hy := @whyperbolic_space.dist_conv _ _ _ x y y ha0 ha1, 
      rw [dist_self x, mul_zero, zero_add] at hx,
      rw [dist_self y, mul_zero, add_zero, dist_comm y x] at hy,
      have hxy := add_le_add hx hy,
      have : a * dist x y + (1 - a) * dist x y = dist x y := by linarith,
      rw this at hxy, clear this,
      have htriangle := dist_triangle_right x y (wmap a x y),
      split;
      { have := antisymm htriangle hxy, linarith, },
    end 

    @[simp]
    lemma dist_self_wmap_left : dist x (wmap a x y) = a * (dist x y) := 
    and.left $ dist_self_wmap ha0 ha1

    @[simp]
    lemma dist_self_wmap_right : dist y (wmap a x y) = (1 - a) * (dist x y) := 
    and.right $ dist_self_wmap ha0 ha1

    @[simp]
    lemma wmap_self : wmap a x x = x :=
    begin 
      have htriangle := whyperbolic_space.dist_conv x x x ha0 ha1,
      rw [dist_self, mul_zero, mul_zero, add_zero] at htriangle,
      exact eq.symm (dist_le_zero.mp htriangle),
    end

    lemma wmap_same_coeff_same_firt : dist (wmap a x y) (wmap a x z) ≤  a * (dist y z) := 
    begin 
      have := whyperbolic_space.same_coeff x x y z ha0 ha1,
      rw [dist_self, mul_zero, zero_add] at this,
      exact this,
    end
    
  omit ha0 ha1

  @[simp]
  lemma wmap_zero : wmap 0 x y = x := 
  begin
    have : dist x (wmap 0 x y) = 0 * dist x y := dist_self_wmap_left rfl.ge zero_le_one,
    rw [zero_mul] at this,
    exact (dist_eq_zero.mp this).symm,
  end

  @[simp]
  lemma wmap_one : wmap 1 x y = y :=
  begin 
    have : dist y (wmap 1 x y) = (1 - 1) * (dist x y) := dist_self_wmap_right zero_le_one rfl.ge,
    rw [sub_self, zero_mul] at this,
    exact (dist_eq_zero.mp this).symm,
  end


  include ha0 ha1 hb0 hb1 
  
    lemma dist_wmap : dist (wmap a x z) (wmap b y w) ≤ (1 - a) * (dist x y) + a * (dist z w) + (abs $ a - b) * (dist y w) := 
    begin 
      set s := (wmap a x z),
      set t := (wmap b y w),
      have h₁ := dist_triangle s (wmap a y w) t,
      have this := same_points y w ha0 ha1 hb0 hb1,
      rw this at h₁, clear this,
      have : dist s (wmap a y w) ≤ (1 - a) * dist x y + a * dist z w := same_coeff _ _ _ _ ha0 ha1,
      linarith,
    end

    lemma dist_wmap_same_first : dist (wmap a x z) (wmap b x w) ≤ a * (dist z w) + (abs $ a - b) * (dist x w) := 
    begin
      have := @dist_wmap _ _ _ _ x x z w ha0 ha1 hb0 hb1,
      rw [dist_self] at this,
      linarith,
    end

  omit ha0 ha1 hb0 hb1 
  

end basic_lemmas

end whyperbolic_space