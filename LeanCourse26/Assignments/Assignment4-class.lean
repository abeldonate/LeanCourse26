module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Function Set

#click_suggestions

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

/-! # Exercises to hand-in. -/

section

-- In class, we saw that Lean does not accept definitions like this:
-- def wrong : ℕ → ℕ
--  | n => 1 + wrong (n + 1)

-- In this case, you can actually derive a contradiction from a function with this property.
-- Do so in the following exercise.
lemma contradictory_definition (f : ℕ → ℕ) (h : ∀ n : ℕ, f n = 1 + f (n + 1)) : False := by
  have h2 : ∀ k, f k + k = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [h k] at ih
      linarith
  have h3 := h2 (f 0 + 1)
  linarith


lemma contradictory_definition' (f : ℕ → ℕ) (h : ∀ n : ℕ, f n = 1 + f (n + 1)) : False := by
  let min := argmin f
  have hmin : f min ≤ f (min + 1) := argmin_le f (min + 1)
  have hstep := h (min)
  omega




-- Hint for the exercise `contradictory_definition`:
-- use the hypothesis to study `f 0`: can you relate it to `f 1`, `f 2`, etc.?
-- Perhaps you can formulate a hypothesis and prove it by induction.

lemma sum_triang (n : ℕ) : (∑ i ∈ Finset.range (n + 1), (i : ℚ)) = n * (n + 1) / 2 := by
    induction n with
    | zero => simp
    | succ m hm =>
      rw [Finset.sum_range_succ, hm]
      field_simp
      norm_cast
      ring

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ 3) = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 := by
  rw [sum_triang]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    field_simp
    norm_cast
    ring


end

section

-- Let's define a new operation on points in ℝ⁴.

@[ext]
structure Point4 where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ
-- x : 1, y : i, z : j, w : k

def op (a b : Point4) : Point4 where
  x := a.x * b.x - a.y * b.y - a.z * b.z - a.w * b.w
  y := a.x * b.y + a.y * b.x + a.z * b.w - a.w * b.z
  z := a.x * b.z - a.y * b.w + a.z * b.x + a.w * b.y
  w := a.x * b.w + a.y * b.z - a.z * b.y + a.w * b.x

-- Prove that op is associative.
lemma op_assoc {a b c : Point4} : op (op a b) c = op a (op b c) := by
  ext <;> simp [op] <;> ring

-- Investigate whether op is commutative: prove one of the following.
lemma op_comm : ∀ a b : Point4, op a b = op b a := by
  sorry

lemma not_op_comm : ¬(∀ a b : Point4, op a b = op b a) := by
  push Not
  use ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩
  intro h
  simp [op] at h
  linarith








-- For the latter, you may the following helpful.
example : ⟨0, 1, 2, 3⟩ ≠ (⟨0, 3, 2, 3⟩ : Point4) := by
  sorry

example {x y : ℝ} (h : x ≠ y) : ⟨0, 1, x, 3⟩ ≠ (⟨0, 1, y, 3⟩ : Point4) := by
  sorry

-- If you want to use one of these lemmas, prove it also.
lemma ne_of_ne_x {a b : Point4} (h : a.x ≠ b.x) : a ≠ b := by
  sorry
lemma ne_of_ne_y {a b : Point4} (h : a.y ≠ b.y) : a ≠ b := by
  sorry
lemma ne_of_ne_z {a b : Point4} (h : a.z ≠ b.z) : a ≠ b := by
  sorry
lemma ne_of_ne_w {a b : Point4} (h : a.w ≠ b.w) : a ≠ b := by
  sorry


section Bipointed

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/




-- give the definition here
structure Bipointed where
  a : Point
  b : Point
  neq : a ≠ b

-- state and prove the lemma here
example {BP : Bipointed} : ∀ z, z ≠ BP.a ∨ z ≠ BP.b := by
  intro z
  by_cases h : z ≠ BP.a
  · left
    exact h
  · push Not at h
    rw [h]
    right
    exact BP.neq

end Bipointed
