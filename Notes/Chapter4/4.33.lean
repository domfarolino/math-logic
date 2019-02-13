-- Building Natural Deduction Proofs
-- 4.33 Disjunction

variables A B: Prop

-- The or-introduction rules (to introduce an ∨ from a premise) we use or.inl
-- and or.inr
--   - or.inl keeps the premise as the left ("l") side
--   - or.inr keeps the premise as the right ("r") side

variable h: A
example: A ∨ B := show A ∨ B, from or.inl h

-- Or-elimination is tougher. Assume we have the premise A ∨ B. Going forwards,
-- if you need to prove something (C) from A ∨ B, you have to have three proofs:
--   - A proof of A ∨ B (duh)
--   - A proof of C from A
--   - A proof of C from B
--  Once we satisfy these requirements, we can use or.elim on |h|.

-- Intro our new variable.
variable C: Prop

-- Satisfy our three requirements.
variable h1: A ∨ B
variable ha: A -> C
variable hb: B -> C

-- Now let's prove |C| from our hypotheses.
example: C :=
or.elim h1
  (assume assumeA: A, show C, from (ha assumeA))
  (assume assumeB: B, show C, from (hb assumeB))

-- This sort of thing goes forward (think top-down in the natural deduction
-- proofs).