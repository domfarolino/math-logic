-- 5.1 Proof by Contradiction (and Classical Reasoning)

-- We are givent he tool `by_contradiction` in Lean, under the classical
-- reasoning "toolbox".

open classical

variable A: Prop

-- Proofs by contradiction are of the following form:
example: A :=
by_contradiction
(assume h: ¬ A,
show false, from sorry)

-- An important consequence of this rule is the law of the excluded middle.
-- We can prove this law, aka, we can prove A or ¬ A, with proof by
-- contradiction:

example: A ∨ ¬ A :=
by_contradiction -- Can assume this since contradiction
(assume h1: ¬ (A ∨ ¬ A),
  have hna: ¬ A, from
    assume ha: A,
    have hAOrNA: A ∨ ¬ A, from or.inl ha,
    show false, from h1 hAOrNA, -- Assume A, since we have a negative. This is derived from the ND proof.
  have hAOrNA2: (A ∨ ¬ A), from or.inr hna,
  show false, from h1 hAOrNA2)

  -- Notice we shows that we "have" ¬ A, by showing false in the "inner" proof.
  -- This is how the normal non-proof-by-contradiction rules work. Remember
  -- https://leanprover.github.io/logic_and_proof/propositional_logic_in_lean.html#negation?