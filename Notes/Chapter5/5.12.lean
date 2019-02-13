-- 5.2 Some Classical Principles

open classical

variables A B: Prop

-- If |A -> B| is any implication, |¬ B -> ¬ A| is known as the contrapositve.
-- Every implication implies its contrapositive, and the other direction is
-- true classically.

-- Forward intuitionistic proof:

example: (A -> B) -> (¬ B -> ¬ A) :=
assume h1: (A -> B),
  show (¬ B -> ¬ A), from
    assume hNotB: ¬ B,
    show ¬ A, from
      assume hA: A,
      show false, from hNotB (h1 hA)


-- Classical contrapositive:

example: (¬ B -> ¬ A) -> (A -> B) :=
assume h1: (¬ B -> ¬ A),
show (A -> B), from -- Just descriptive af.
assume hA: A,
  show B, from by_contradiction(
    assume hB: ¬ B,
    have hNotA: ¬ A, from h1 hB,
    show false, from hNotA hA)