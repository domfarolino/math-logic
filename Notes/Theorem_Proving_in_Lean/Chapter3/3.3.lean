-- 3.3 Propositional Logic

-- This section of notes mostly covers syntactic sugar, since the
-- content is largely the same as in Chapter 2.

constants p q: Prop

-- Some fancy stuff, but structurally identical to what we already know.
example (h: p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

-- From 3.3.3 Negation and Falsity

-- The following proof is invalid:
-- example (hp: p) (hnp: ¬ p): q := show false, from hnp hp
-- But we can modify it to say that from false, anything is true:

example (hp: p) (hnp: ¬ p): q :=
  have hf: false, from hnp hp,
  show q, from false.elim hf

-- Or more simply:
example (hp: p) (hnp: ¬ p): q :=
  false.elim (hnp hp)

-- The pattern of deriving an arbitrary fact from false is represented
-- by "absurd". The below example is the same as above:

example (hp: p) (hnp: ¬ p): q := absurd hp hnp

-- From 3.3.4 Logical Equivalence

namespace log_equiv
  -- We are creating this namespace here, so we can make |p| and |q|
  -- variables, and not constants.
  variables p q: Prop

  -- Implicitly consumes universally-quantified parameters because
  -- |p| and |q| are variables. We could use constants, and have Pi
  -- types, or an explicit ∀.
  theorem and_swap: p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume h: p ∧ q,
        show q ∧ p, from and.intro h.right h.left)
      (assume h: q ∧ p,
        show p ∧ q, from and.intro h.right h.left)

  constants a b : Prop
  theorem and_swap_constants: ∀ (a b: Prop), a ∧ b ↔ b ∧ a :=
    fun (a b: Prop),
    iff.intro
      (assume h: a ∧ b,
        show b ∧ a, from and.intro h.right h.left)
      (assume h: b ∧ a,
        show a ∧ b, from and.intro h.right h.left)

  #check and_swap
  #check and_swap p q
  #check and_swap a b

  #check and_swap_constants
  #check and_swap_constants p q
  #check and_swap_constants a b

  example (h: p ∧ q): q ∧ p := (iff.mp (and_swap p q)) h
end log_equiv