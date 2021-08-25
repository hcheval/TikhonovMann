import data.list
import tactic.basic
import data.finset.basic
import data.real.basic

open lean lean.parser tactic interactive interactive.types expr

meta def tactic.specialize_single (n : name) (l : loc) : tactic unit := do
  val ← get_local n,
  valt ← infer_type val,
  hs ← l.get_locals,
  hs.mmap' (λ h, do
    ht ← infer_type h,
    try $ match ht with
      | (pi _ _ vt _) := do
        is_def_eq vt valt >> note (h.local_pp_name ++ n) none (h.mk_app [val]) >> pure ()
      | (lam _ _ vt _) := do
        is_def_eq vt valt >> note (h.local_pp_name ++ n) none (h.mk_app [val]) >> pure ()
      | _ := pure ()
    end)

meta def tactic.specialize_all (hs : list simp_arg_type) (l : loc) : tactic unit := do
  (lp, ln, ln', b) ← decode_simp_arg_list hs,
  lp.mmap' (λ e, do
    e ← to_expr e,
    if e.is_local_constant then tactic.specialize_single e.local_pp_name l
      else pure ()),
  if !b then pure () else (do
    ls ← tactic.local_context,
    ls.mmap' (λ e, do
      if expr.is_local_constant e then tactic.specialize_single e.local_pp_name l else pure ()),
    pure ())

namespace tactic.interactive

meta def specialize_all1 (val : parse ident) (loc : parse location) : tactic unit :=
tactic.specialize_single val loc

meta def specialize_all (vals : parse simp_arg_list) (loc : parse location) : tactic unit :=
tactic.specialize_all vals loc

end tactic.interactive

example {α β γ : Type*}
  (f : α → β)
  (g : α → β)
  (h : β → γ)
  (x y : α) (z : β) : γ := begin
    specialize_all [*] at *,
    extract_goal,
    exact h.z
  end

namespace tactic.interactive

  meta def ls := library_search
  meta def ss := squeeze_simp

end tactic.interactive

@[reducible]
def max3 (x y z : ℕ) : ℕ := list.foldr max 0 [x, y, z] 

variables {x y z : ℕ}

lemma max3_le₁ : x ≤ max3 x y z := by simp [max3]

lemma max3_le₂ : y ≤ max3 x y z := by simp [max3]

lemma max3_le₃ : z ≤ max3 x y z := by simp [max3]

lemma mul_sides_left (a b c : ℝ) (h₁ : 0 ≤ a) (h₂ : 0 ≤ c) : a ≤ b → c * a ≤ c * b := by {
  intros h,
  apply mul_le_mul (le_of_eq rfl) h h₁ h₂,
}

open_locale big_operators 
open finset (range)

lemma nonneg_sub_of_nonneg_sum (x : ℕ → ℝ) (n j : ℕ) (x_nonneg : ∀ i, 0 ≤ x i)
  : 0 ≤ (∑ i in finset.range (n + j), (x i)) - (∑ i in finset.range n, (x i)) :=
begin 
  have h₁ : range n ≤ range (n + j) := finset.range_mono le_self_add,
  have : (∑ i in finset.range n, (x i)) ≤ (∑ i in finset.range (n + j), (x i)) := by {
    have := @finset.sum_mono_set_of_nonneg ℕ ℝ _ x x_nonneg,
    specialize this h₁,
    dsimp only at this,
    exact this,
  },
  exact sub_nonneg.mpr this,
end

lemma helper (a b c : ℝ) : a * b ≤ c → b ≤ (1 / a) * c := by {
  intros h,
}


