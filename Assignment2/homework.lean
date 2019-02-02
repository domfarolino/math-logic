-- Assignment 2
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic
-- At the time of writing, all of these are correct, and give no erroneous
-- output in Lean, except the final proof, which indicates a sorry is used,
-- because I have not completed it yet.

variables A B C D : Prop

section
  example: A ∧ (A → B) → B :=
    assume h: A ∧ (A → B),
    have hA: A, from and.left h,
    show B, from (and.right h) hA
end

section
  example: A → ¬ (¬ A ∧ B) :=
    assume ha: A,
    assume h2: ¬ A ∧ B,
    show false, from (and.left h2) ha -- One of our assumptions from the ND proof
end

-- Somewhat reminiscent of
-- https://leanprover.github.io/logic_and_proof/propositional_logic_in_lean.html#examples
-- in that it only needs to stop at |C|, similar to how this proof only needs
-- to stop at |false|.
section
  example: ¬ (A ∧ B) → (A → ¬ B) :=
    assume h: ¬ (A ∧ B),
    assume hA: A,
    assume hB: B,
    -- Here we must show false, and we can do that by
    -- Combining h and (hA ∧ hB)
    show false, from h (and.intro hA hB)
end

-- Very similar to:
-- https://leanprover.github.io/logic_and_proof/propositional_logic_in_lean.html#conjunction
section
  variable h1: A ∨ B
  variable h2: A -> C
  variable h3: B -> D
  example: C ∨ D :=
    or.elim h1
      (assume h: A,
        show C ∨ D, from or.inl (h2 h))
      (assume h: B,
        show C ∨ D, from or.inr (h3 h))
end

-- At first I thought we needed to show false, and then do two or.elim's, but
-- that did not make sense. Reversing it is right.
section
  variable h: (¬ A ∧ ¬ B)
  example: ¬ (A ∨ B) :=
  assume h1: (A ∨ B),
  or.elim h1
    (assume ha: A,
      show false, from (and.left h) ha)
    (assume hb: B,
      show false, from (and.right h) hb)
end

-- I do not know how to do this yet. I think it relies on Chapter 5.
section
example: ¬ (A ↔ ¬ A) :=
sorry
end