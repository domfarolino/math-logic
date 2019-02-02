-- Assignment 1
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

variables A B C D : Prop

-- Exercise 1
section
  example : ¬ (A ∧ B) → (A → ¬ B) :=
  assume h1: ¬ (A ∧ B),
  assume ha: A,
  assume hb: B,
  have hab: (A ∧ B), from and.intro ha hb,
  show false, from h1 hab
end

-- Exercise 2
section
end

-- Exercise 3
section
end