-- Name: <insert your name here>
import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Finite.Basic

open Real Function Set Nat

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: 28.10.2025 at 16:00.
* Solutions from the section `Exercises to hand-in` will receive feedback
  from the tutors.
* None of your solutions should be LLM-generated: doing so will only rob you
  of the practice and waste the tutors' time.
* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (p q r s : Prop) (h : p ∧ q → r) (hp : p) (h' : q → s) : q → r ∧ s := by
  intro hq
  refine ⟨?_,?_⟩
  · exact h ⟨hp,hq⟩
  · exact h' hq

example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by
  intro ⟨x, hp⟩
  exact ⟨x, h x hp⟩

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  contrapose!
  intro h
  omega


/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by
  constructor
  · intro hpr x hp
    exact hpr ⟨x, hp⟩
  · intro hpxr ⟨x, hp⟩
    exact (hpxr x) hp



/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
  constructor
  · intro ⟨x, ⟨hpx, hr⟩⟩
    exact ⟨⟨x, hpx⟩, hr⟩
  · intro ⟨⟨x, hpx⟩, hr⟩
    exact ⟨x, ⟨hpx, hr⟩⟩


/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by
  constructor
  · intro ⟨x, hx⟩ hall
    exact hall x hx
  · intro h
    by_contra hne
    apply h
    intro x hx
    exact hne ⟨x, hx⟩


def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun _ : ℕ ↦ a) a := by
  unfold SequentialLimit
  intro eps heps
  use 0
  intro n hn
  rw [sub_self]
  rw [abs_zero]
  positivity


/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  calc (n)! ∣ (m)! := Nat.factorial_dvd_factorial h
    _ ∣ (m + 1)! := Nat.factorial_dvd_factorial (Nat.le_succ m)

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by
  gcongr
  · linarith
  · linarith

-- Use `rw?` or `#click_suggestions` to help you in the following calculation.
-- Alternatively, write out a calc block by hand.
example {G : Type*} [Group G] {a b c : G}
    (h : a⁻¹ * b * c * c⁻¹ * a * b⁻¹ * a * a⁻¹ = b) (h' : b * a = a * b) : b = 1 := by
  rw [mul_inv_cancel_right, mul_inv_cancel_right, mul_assoc a⁻¹ b a, h', inv_mul_cancel_left,
    mul_inv_cancel] at h
  exact h.symm

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  constructor
  · intro h
    linarith
  · intro h
    linarith


/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
  calc
    n - m ^ 2 ≤ n - 0 := by gcongr; exact sq_nonneg m
    _ ≤ n + 3 := by linarith

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  have h2 := h 2
  linarith



/-! # Exercises to hand-in. -/

section Logic
-- Prove the following statements with basic tactics,
-- in particular without using `tauto`, `grind` or lemmas from Mathlib.

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ) := ∀ x, ContinuousAtPoint f x

-- Exercise for you. Remember that you can use `unfold` to expand a definition.
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
  unfold Continuous'
  constructor
  · intro h x
    exact (hfg x).mp (h x)
  · intro h x
    exact (hfg x).mpr (h x)


def All (p : ℝ → Prop) := ∀ x, p x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    All p ↔ All q := by
  constructor
  unfold All
  · intro h2 x
    exact (h x).mp (h2 x)
  · intro h2 x
    exact (h x).mpr (h2 x)




example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    (∃ x, p x) ↔ (∃ x, q x) := by
  constructor
  · intro ⟨x, hpx⟩
    exact ⟨x, (h x).mp hpx⟩
  · intro ⟨x, hpx⟩
    exact ⟨x, (h x).mpr hpx⟩

-- Is the following true? If yes, prove it in Lean.
-- If not, give a counterexample and prove it. (What do you have to do to do so?)
-- example (p q : ℕ → Prop) (h: (∃ x, p x) ↔ (∃ x, q x)) : ∀ x, p x ↔ q x := by
--   sorry
-- This is false: take `p x := x = 0` and `q x := x = 1`. Both sides of `h` are true,
-- but `p 0` holds while `q 0` does not. To show this in Lean, we prove the negation
-- of the statement, quantified over all `p` and `q`.
example : ¬ ∀ (p q : ℕ → Prop), ((∃ x, p x) ↔ (∃ x, q x)) → ∀ x, p x ↔ q x := by
  intro h
  have h0 := h (fun x ↦ x = 0) (fun x ↦ x = 1) ⟨fun _ ↦ ⟨1, rfl⟩, fun _ ↦ ⟨0, rfl⟩⟩ 0
  simp at h0



/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro ⟨x, hpq⟩
    cases hpq with
    | inl hp =>
      left
      exact ⟨x, hp⟩
    | inr hq =>
      right
      exact ⟨x, hq⟩
  · intro hpq
    cases hpq with
    | inl hpx =>
      obtain ⟨x, hp⟩ := hpx
      use x
      left
      exact hp
    | inr hqx =>
      obtain ⟨x, hq⟩ := hqx
      use x
      right
      exact hq

end Logic

section Functions

-- Let us investigate the function example from the lecture further.

-- This is how to say "a natural number p is prime" in Mathlib.
#check Nat.Prime

-- The following theorem is the key ingredient to it.
-- (You have not seen the syntax `[hp: Fact (Nat.Prime p)]` yet:
-- this is related to implicit arguments.
-- You can assume it says `(hp: Nat.Prime p)`. We will discuss the precise difference later.)
--
-- Use `exact?`, `apply?` or `#click_suggestions` to find this theorem in Mathlib.
-- Describe what you are doing.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x := by
  exact ZMod.pow_card x

-- The above theorem has a name. What is it?
-- Use this name to find the same result using leansearch.net.
-- Describe every step you're performing.

-- We go to the definition of `ZMod.pow_card`: hover over the theorem,
-- right-click and select "Go to definition".
-- This opens the Mathlib file where this theorem is proven. The theorem's doc-string says
-- "/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/".
-- This is the name of the theorem: Fermat's little theorem.

-- We open leansearch.net, type "Fermat's little theorem" as a query and press search.
-- The fourth result we get is `ZMod.pow_card x`, with the description
-- "Fermat's Little Theorem in Z/pZ: x^p=x"


-- Use `exact?` to find the following theorem in Mathlib.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (k : ZMod p) (hk : k ≠ 0) : k ^ (p - 1) = 1 := by
  exact ZMod.pow_card_sub_one_eq_one hk

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] :
    (fun x ↦ x ^ p + 2 * x ^ (2 * (p - 1) + 1) : ZMod p → ZMod p) = (fun x ↦ 3 * x) := by
  ext x
  rw [ZMod.pow_card, pow_succ, pow_mul']
  by_cases hx : x = 0
  · simp [hx]
  · rw [ZMod.pow_card_sub_one_eq_one hx]
    ring




-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (3 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one hk, one_pow, one_mul]

example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (5 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one hk, one_pow, one_mul]

end Functions


/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hs (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := ht (ε / 2) (by linarith)
  use max N₁ N₂
  intro n hn
  have h₁ := hN₁ n (le_of_max_le_left hn)
  have h₂ := hN₂ n (le_of_max_le_right hn)
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr 1; ring
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  by_cases hc : c = 0
  · intro ε hε
    use 0
    intro n _
    simp [hc, hε]
  · intro ε hε
    have hc' : 0 < |c| := abs_pos.mpr hc
    obtain ⟨N, hN⟩ := hs (ε / |c|) (div_pos hε hc')
    use N
    intro n hn
    calc |c * s n - c * a| = |c| * |s n - a| := by rw [← mul_sub, abs_mul]
      _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hN n hn) hc'
      _ = ε := by field_simp

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by
  calc
    n + 1 ≤ 3 - m ^ 2 := by linarith
    _ ≤ 3 - 0 := by gcongr; exact sq_nonneg m
    _ = 3 + 0 := by ring
    _ ≤ 3 + k ^ 2 := by gcongr; exact sq_nonneg k


section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intro n hn
  show k * s n ≤ n * s n
  gcongr

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro k
  obtain ⟨N₁, hN₁⟩ := h₁ k
  obtain ⟨N₂, hN₂⟩ := h₂ k
  use max N₁ N₂
  intro n hn
  rw [Pi.add_apply, Pi.add_apply, mul_add]
  exact _root_.add_le_add (hN₁ n (le_of_max_le_left hn)) (hN₂ n (le_of_max_le_right hn))

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  -- The factorial works: `(n + 1)! = (n + 1) * n !`.
  refine ⟨fun n ↦ (n)!, ?_, fun n ↦ (Nat.factorial_pos n).ne'⟩
  intro k
  use k
  intro n hn
  show k * (n)! ≤ (n + 1)!
  rw [Nat.factorial_succ]
  gcongr
  omega




end Growth
