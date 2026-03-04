example (P Q : Prop) (p : P) : P := by exact p

example : 3 + 2 = 5 := by rfl

example (m : M) : M := by exact m
example (m : M) : M := m


example (P Q : Prop) (h: P → Q) (p : P) : Q := h p
example (P Q : Prop) (h: P → Q) (p : P) : Q := by
  apply h p
  
example (P Q R : Prop) (h₁: P → Q) (h₂: Q → R) (p : P) : R :=
  (h₂ ∘ h₁) p

example (P Q R : Prop) (h₁: P → Q) (h₂: Q → R) (p : P) : R :=
  h₂ $ h₁ p


example (P: Prop) : P → P := by
  intro p
  exact p

example (P: Prop) : P → P := id

example (P: Prop) : P → P := fun p ↦ p

#check id

example : (fun (x : Type) ↦ x) = id := by rfl

/-
## Exercise Block 2
-/

-- Exercise 2.1
-- Show, in at least two different ways, that if
-- `P` implies `Q` and `Q` implies `R`, then `P` implies `R`

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R :=
  h₂ $ h₁ p

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) : P → R := h₂ ∘ h₁

-- Exercise 2.2
-- Show that if `P` implies `Q`, `Q` implies `R`, and
-- `R` implies `S`, then `P` implies `S`

example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) (p : P) : S :=
  h₃ $ h₂ $ h₁ p

example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := h₃ ∘ h₂ ∘ h₁

-- Exercise 2.3
-- Show that if `P` implies that `Q` implies `R`
-- and that `P` implies `Q`, then `P` implies `R`.

example (P Q R : Prop) (h₁ : P → (Q → R)) (h₂ : P → Q) : P → R := by
  intro p
  apply h₁ p (h₂ p)

example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R :=
  fun p ↦ h₁ p (h₂ p)


-- Exercise 2.4 (Master students)
example (P Q R : Prop) (h₂ : Q → R) : P → (Q → R) := by
  intro p
  exact h₂

example (P Q R : Prop) (h₂ : Q → R) : P → (Q → R) := fun p ↦ h₂

-- Exercise 2.5 (Master students)
example (P Q R S : Prop) (h₂ : Q → R) : S → P → Q → R := by
  intro s p q
  apply h₂ q

example (P Q R S : Prop) (h₂ : Q → R) : S → P → Q → R := fun _ _ q ↦ h₂ q

example (P Q R S : Prop) (h₂ : Q → R) : S → P → Q → R := fun _ _ ↦ h₂


/-
## Exercise Block B03
-/

-- Exercise 3.1
-- Shows how to use `rw` to prove that if `P` and `Q` are equivalent, and `Q` and
-- `R` are equivalent, then `P` and `R` are equivalent (transitivity of `↔`)
example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁,h₂]

-- Exercise 3.2
-- Shows how to use `rw` to prove that if `P` and `Q` are equivalent, and `Q` and `R`
-- are equivalent, then `P` and `R` are equivalent (transitivity of `↔`)
example (P Q : Prop) (h : Q ↔ P) : P → Q := by
  rw [h]
  exact id

-- Exercise 3.3
-- Given four equivalent propositions in a cycle, prove that the first
-- implies the last. You will need reverse rewriting (`← h`) or `symm`,
-- and rewriting at hypotheses (`rw [...] at`).
example (P Q R S : Prop) (h₁ : P ↔ Q) (h₂ : R ↔ Q) (h₃ : R ↔ S) (p : P) : S := by
  rw [h₁, h₂.symm, h₃] at p
  exact p

example (P Q R S : Prop) (h₁ : P ↔ Q) (h₂ : R ↔ Q) (h₃ : R ↔ S) (p : P) : S :=
  h₃.mp $ h₂.mpr $ h₁.mp p

theorem test (P Q R S : Prop) (h₁ : P ↔ Q) (h₂ : R ↔ Q) (h₃ : R ↔ S) (p : P) : S := by
  rw [h₃.symm, h₂, h₁.symm]
  exact p

#print test

theorem test2 (P Q R : Prop) (h₁ : P ↔ Q) : Q ↔ P := by
  rw [h₁]

#print test2



/-
# Exercise Block 4

Turn all of the previous exercises into term mode proofs.
-/

-- Exercise 4.1
-- Chain three implications together: if we can go from `P` to `Q` to `R` to `S`,  then `P → S`
example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := h₃ ∘ h₂ ∘ h₁ 
example (P Q R S : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S := by
  intro p
  exact h₃ $ h₂ $ h₁ p

-- Exercise 4.2
-- Nested implications: if `P` implies `(Q → R)` and `P` implies `Q`, then `P` implies `R`
example (P Q R : Prop) (h₁ : P → Q → R) (h₂ : P → Q) : P → R := λ p ↦ h₁ p (h₂ p)

-- Exercise 4.3 (Master)
-- Try turning this tactic mode proof into term mode, first without using
-- `#print' and then using it
example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁.symm] at h₂
  exact h₂

example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁.symm] at h₂
  exact h₂

theorem test_rewriting (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := by
  rw [h₁.symm] at h₂
  exact h₂

#print test_rewriting

example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R :=
  Eq.mp (congrArg (fun _a ↦ _a ↔ R) (propext (Iff.symm h₁))) h₂

example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R :=
  (congrArg (fun _a ↦ _a ↔ R) (propext h₁.symm)).mp h₂

-- This does not work
-- example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := h₁ ▸ h₂

example (P Q R : Prop) (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R := h₁.trans h₂
