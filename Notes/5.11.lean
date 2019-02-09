-- 5.1 Proof by Contradiction (and Classical Reasoning) continued

-- Proof by contradiction is the same as the principle: ¬¬ A ↔ A. From right to
-- left, this holds intuitionistically:

open classical

variables A B: Prop

example: A -> ¬¬ A :=
assume hA: A,
show ¬¬ A, from
  assume hNA: ¬ A, hNA hA -- (false, in the ND proof).

-- The other direction we must prove with classical reasoning.

example: ¬¬ A -> A :=
assume h1: ¬¬ A,
show A, from by_contradiction(
  assume h2: ¬ A, -- Doing this because we're in contradiction "mode".
  show false, from h1 h2
)

-- Putting it together:
example: A <-> ¬¬ A :=
iff.intro
  (assume hA: A, -- Intuitionistic, must do this version first.
  show ¬¬ A, from
    assume hNA: ¬ A, hNA hA)
  (assume h1: ¬¬ A, -- By contradiction
  show A, from by_contradiction(
    assume h2: ¬ A,
    show false, from h1 h2
  ))