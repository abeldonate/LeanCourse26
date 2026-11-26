module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: **Wednesday**, 25.11.2025 at 16.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to hand in -/

variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup

section conjugate

/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
-- THIS
def conjugate (x : G) (H : Subgroup G) : Subgroup G :=
  {
  carrier := {x * h * x⁻¹ | h ∈ H}
  mul_mem' a b := by
    obtain ⟨a, ha, rfl⟩ := a
    obtain ⟨b, hb, rfl⟩ := b
    simp
    exact mul_mem ha hb
  one_mem' := by simp
  inv_mem' {g} hg := by
    obtain ⟨h, hh, rfl⟩ := hg
    simp
    use h⁻¹
    exact ⟨inv_mem hh, by group⟩

  }

-- Characterise normal subgroups in terms of your definition.
example {H : Subgroup G} : H.Normal ↔ ∀ x, conjugate x H = H := by
  constructor
  · intro hnormal x
    ext h
    constructor
    · rintro ⟨h, hH, rfl⟩
      apply hnormal.conj_mem _ hH
    · intro hconj
      simp [conjugate]
      use x⁻¹ * h * x
      constructor
      · have aux := hnormal.conj_mem h hconj (x⁻¹)
        group at aux ⊢
        exact aux
      group
  · intro H
    exact normal_iff_map_conj_eq.mpr H

/- Prove the following lemmas. In the language of group action (next Tuesday), they prove that
a group acts on its own subgroups by conjugation. -/

-- THIS
lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext
  simp [conjugate]

-- THIS
lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by
  ext
  simp [conjugate]
  group


end conjugate

section finite

section

variable {G : AddSubgroup ℚ}

-- In this section, you will prove a nice group theory fact: `(ℚ, +)` has no non-trivial subgroup
-- of finite index: any finite index subgroup must be `⊤`. Follow the steps below.

-- In the proof we will consider the following subgroup, consisting of all `n`-fold multiples
-- of rational numbers.
-- THIS
def multiple (n : ℕ) : AddSubgroup ℚ :=
{
  carrier := {n * q | q : ℚ}
  add_mem' x y := by
    obtain ⟨x, hx, rfl⟩ := x
    obtain ⟨y, hy, rfl⟩ := y
    use x + y
    linarith
  zero_mem' := by simp
  neg_mem' x := by
    obtain ⟨x, hx, rfl⟩ := x
    simp
    use -x
    simp
}

-- If your definition above is correct, this proof is true by rfl.
lemma mem_multiple_iff (n : ℕ) (q : ℚ) : q ∈ multiple n ↔ ∃ r, n * r = q := by rfl

-- The next lemma is a general fact from group theory: use mathlib to find the right lemma.
-- Hint: it's similar to `Subgroup.pow_index_mem`.

-- One approach: do `#check Subgroup.pow_index_mem`, go to definition and find the additive version.
#check AddSubgroup.nsmul_index_mem

lemma step1 {n : ℕ} (hG : G.index = n) (q : ℚ) : n • q ∈ G := by
  rw [← hG]
  exact AddSubgroup.nsmul_index_mem G q

lemma step2 {n : ℕ} (hG : G.index = n) : multiple n ≤ G := by
  intro x
  intro ⟨y, hy⟩
  rw [← hy]
  apply step1 hG

lemma step3 {n : ℕ} (hn : n ≠ 0) : multiple n = ⊤ := by
  ext q
  simp [multiple]
  use q / n
  field_simp

-- The goal of this exercise: (ℚ, +) has no non-trivial subgroups of finite index.
-- THIS
example (hG : G.index ≠ 0) : G = ⊤ := by
  apply le_antisymm
  · simp
  · rw [← step3 hG]
    exact step2 rfl

end

section frobenius

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
open Nat Finset

-- THIS
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p) := by
    ext (_|_) <;> simp [hp.out.pos]
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i hi
    simp at hi
    apply hp.out.dvd_choose_self hi.1.ne' hi.2
  have : ∑ i ∈ Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
    calc
     _ =  ∑ i ∈ Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by
       congr! with i hi
       exact (CharP.cast_eq_zero_iff R p (p.choose i)).mpr (dvd_choose i hi)
     _ = 0 := by
       simp
  simp [add_pow, Finset.sum_range_succ, range_eq_insert_Ioo, sum_insert, this, add_comm]

end frobenius
