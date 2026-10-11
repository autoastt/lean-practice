/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
  assume ha : a
  show a from
    ha

theorem K (a b : Prop) :
    a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume habc : a → b → c
  assume hb : b
  assume ha : a
  show c from
    habc ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  assume ha : a
  assume ha' : a
  show a from
    ha

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  assume ha : a
  assume ha' : a
  show a from
    ha'

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  assume habc : a → b → c
  assume ha : a
  assume hac : a → c
  assume hb : b
  show c from
    hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : ¬ b
  assume ha : a
  have hb : b :=
    hab ha
  show False from
    hnb hb

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (assume h : ∀x, p x ∧ q x
     have hp : ∀x, p x :=
       fix x : α
       And.left (h x)
     have hq : ∀x, q x :=
       fix x : α
       And.right (h x)
     show (∀x, p x) ∧ (∀x, q x) from
       And.intro hp hq)
    (assume h : (∀x, p x) ∧ (∀x, q x)
     fix x : α
     show p x ∧ q x from
       And.intro (And.left h x) (And.right h x))

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume hex : ∃x, ∀y, p x y
  fix b : α
  show ∃x, p x b from
    Exists.elim hex
      (fix a : α
       assume hall : ∀y, p a y
       show ∃x, p x b from
         Exists.intro a (hall b))


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
    (a + b) * (a + b)
    _ = a * (a + b) + b * (a + b) :=
      by rw [Nat.add_mul]
    _ = a * a + a * b + b * a + b * b :=
      by rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    _ = a * a + a * b + a * b + b * b :=
      by rw [Nat.mul_comm b a]
    _ = a * a + 2 * a * b + b * b :=
      by rw [Nat.two_mul, Nat.add_mul, Nat.add_assoc (a * a)]

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have h₁ : (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
    by rw [Nat.add_mul]
  have h₂ : a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b :=
    by rw [Nat.mul_add, Nat.mul_add]; ac_rfl
  have h₃ : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
    by rw [Nat.mul_comm b a]
  have h₄ : a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
    by rw [Nat.two_mul, Nat.add_mul, Nat.add_assoc (a * a)]
  show (a + b) * (a + b) = a * a + 2 * a * b + b * b from
    Eq.trans h₁ (Eq.trans h₂ (Eq.trans h₃ h₄))


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
    False :=
  have hall : ∀x : ℕ, x = 0 ∧ True :=
    Iff.mpr (All.one_point_wrong 0 (fun _ ↦ True)) True.intro
  have h10 : 1 = 0 :=
    And.left (hall 1)
  show False from
    Nat.one_ne_zero h10

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False :=
  have hex : ∃x : ℕ, x = 0 → False :=
    Exists.intro 1
      (assume h10 : 1 = 0
       show False from
         Nat.one_ne_zero h10)
  show False from
    Iff.mp (Exists.one_point_wrong 0 (fun _ ↦ False)) hex

end LoVe
