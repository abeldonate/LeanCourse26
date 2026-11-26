-- Name: <insert your name here>

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Function Set

#click_suggestions



/-! # Exercises to hand-in. -/


noncomputable section choice

variable {α β γ : Type} {f : α → γ} {g : β → γ}

/- In mathematics, we often identify two sets by realizing them as the
same subset of some larger set. Construct, using the axiom of choice,
such an equivalence.
Hint: it might be useful to define auxilliary functions and lemmas that
can be used in the main proof body
-/

lemma exists_preimage (h : range f = range g) (a : α) : ∃ b : β, g b = f a := by
  have h1 : f a ∈ range g := by
    rw [← h]
    exact mem_range_self a
  exact h1

def map_ab (h : range f = range g) (a : α) : β :=
  Classical.choose (exists_preimage h a)

lemma mapab_spec (h : range f = range g) (a : α) : g (map_ab h a) = f a :=
  Classical.choose_spec (exists_preimage h a)

example (hf : Injective f) (hg : Injective g) (H : range f = range g) : α ≃ β :={
  toFun := map_ab H
  invFun := map_ab H.symm
  left_inv a := by
    apply hf
    rw [mapab_spec H.symm, mapab_spec H]
  right_inv b := by
    apply hg
    rw [mapab_spec H, mapab_spec H.symm]
}

end choice


section Subtypes

/-- Let's prove that the positive rationals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use `apply` to use the lemmas about real numbers. -/

abbrev PosRat : Type := {x : ℚ // 0 < x}


instance groupPosRat : Group PosRat where
  one := ⟨1, by positivity⟩
  mul a b := ⟨a.1 * b.1, by positivity [a.2, b.2]⟩
  mul_assoc a b c := by ext; apply mul_assoc
  one_mul a := by ext; apply one_mul
  mul_one a := by ext; apply mul_one
  npow_zero a := by ext; simp
  npow_succ a n := by ext; simp [pow_succ]
  inv a := ⟨a⁻¹, by positivity [a.2]⟩
  inv_mul_cancel a := by ext; apply inv_mul_cancel₀; positivity [a.2]


end Subtypes


section cardinality

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] Finset.card_powerset
#check Finset.induction

lemma finset_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (Finset.powerset s) = 2 ^ Finset.card s := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s h ih =>
    rw [Finset.powerset_insert, Finset.card_union_of_disjoint, Finset.card_image_of_injOn,
        Finset.card_insert_of_notMem h]
    · omega
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_powerset] at hx hy
      have hax : a ∉ x := by
        by_contra
        exact h (hx this)
      have hay : a ∉ y := by
        by_contra
        exact h (hy this)
      rw [← Finset.erase_insert hax, ← Finset.erase_insert hay]
      rw [hxy]
    · rw [Finset.disjoint_left]
      intro s2 h2 h3
      simp at h2 h3
      obtain ⟨w, h4, rfl⟩ := h3
      have ha : a ∈ s := (Finset.insert_subset_iff.mp h2).1
      exact h ha



end cardinality
