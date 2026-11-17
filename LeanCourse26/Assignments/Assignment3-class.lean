import Mathlib.Analysis.Complex.Exponential

open Real Function Set Nat

#click_suggestions

/-

* Hand in the solutions to the exercises below. Deadline: 4.11.2025 before class.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext x
  constructor
  · intro ⟨⟨z, hz, hs⟩, ht⟩
    use z
    refine ⟨⟨hz, ?_⟩, hs⟩
    simp
    rwa [hs]
  · intro ⟨y, ⟨hys, hyt⟩, hfy⟩
    refine ⟨?_, by rwa [← hfy]⟩
    use y




/- Prove this without using lemmas from Mathlib. -/
-- Note: we still use the `simp` tactic... which is using mathlib, but only in a mild way.
-- That's a reasonable compromise for now.
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  simp
  constructor
  · intro h
    obtain ⟨x, ⟨⟨i, hi⟩, hf⟩⟩ := h
    use i
    use x
  · intro h
    obtain ⟨i, ⟨z, ⟨hi, hz⟩⟩⟩ := h
    use z
    exact ⟨⟨i, hi⟩, hz⟩


/- Prove this without using lemmas from Mathlib. -/
example {a b c d : ℝ} (hab : a < b) : Icc a b ⊆ Ioo c d ↔ c < a ∧ b < d := by
  constructor
  · intro h
    have ha : a ∈ Ioo c d := h ⟨by linarith, by linarith⟩
    have hb : b ∈ Ioo c d := h ⟨by linarith, by linarith⟩
    exact ⟨ha.1, hb.2⟩
  · intro ⟨hca, hbd⟩ x ⟨ha, hb⟩
    exact ⟨by linarith, by linarith⟩


/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  ext x
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
  simp [sq_le_sq, le_abs']






section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  constructor
  · intro hgf y
    obtain ⟨x, hx⟩ := hgf y
    use f x
    simpa
  · intro hg z
    obtain ⟨y, hy⟩ := hg z
    obtain ⟨x, hx⟩ := hf y
    use x
    rw [← hy, ← hx]
    simp







/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  intro y
  simp
  obtain ⟨z, hz⟩ := hf ((y - 1) / 2)
  use (z / 3 - 4)
  field_simp
  simp [hz]
  field_simp
  simp





/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  intro h
  let R := {x | x ∉ f x}
  obtain ⟨x, hfx⟩ := h R
  have hiff : x ∈ f x ↔ x ∈ R := by rw [hfx]
  rw [mem_ofPred] at hiff
  tauto

end Surjectivity
