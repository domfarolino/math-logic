-- Assignment 1
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

variables A B C D : Prop

-- Exercise 1
section
  example: ¬ (A ∧ B) → (A → ¬ B) :=
  assume h1: ¬ (A ∧ B),
  assume ha: A,
  assume hb: B,
  have hab: (A ∧ B), from and.intro ha hb,
  show false, from h1 hab
end

-- Exercise 2
section
  example: (A → C) ∧ (B → ¬ C) → ¬ (A ∧ B) :=
  assume h1: (A → C) ∧ (B → ¬ C),
  assume h2: (A ∧ B),
  have hc: C, from (and.left h1) (and.left h2),
  have hnc: ¬ C, from (and.right h1) (and.right h2),
  show false, from hnc hc
end

-- Could also write E2 as this:
section
  example: (A → C) ∧ (B → ¬ C) → ¬ (A ∧ B) :=
  assume h1: (A → C) ∧ (B → ¬ C),
  assume h2: (A ∧ B),
  show false, from
    (show ¬ C, from -- The show is not actually required here
      (and.right h1) (and.right h2))
    (show C, from   -- ^ see above comment
      (and.left h1) (and.left h2))
end

-- Exercise 3
section
end