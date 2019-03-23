-- 3.5 Classical Logic

open classical

variable p: Prop

-- Classical logic adds to our understanding of the constructive rules,
-- the law of the excluded middle: p ∨ ¬ p.

#check em p

-- A consequence of the law of excluded middle is the principle of
-- double-negation. A natural deduction proof of this can be see in
-- 3.4.1.jpg.

theorem dne (h: ¬¬ p): p :=
  (em p).elim -- All we _really_ have is em, so we'll or-elim it.
    (assume hp: p, hp)
    (assume hnp: ¬ p, false.elim (h hnp))

#check dne

-- The reason this works is as follows:
--   1.) The first case, we have to show |p|, and we also get to assume,
--       so that turns out to be trivial.
--   2.) The second case, we get to assume ¬ p. From here, we know that
--       we can create |false|, from (h hnp). We also know that from
--       false, we can prove anything, with false.elim, so we do that.

-- Can also do this my preferred way, by performing
-- proof-by-contradiction. A natural deduction proof of this can be seen
-- in 3.4.2.jpg.

theorem dne2 (h : ¬¬p): p :=
  by_contradiction
    (assume hnp: ¬ p,
    show false, from h hnp)

-- Another example:
variable q: Prop

-- Prove (¬p ∨ ¬q) using (h: ¬(p ∧ q)) and em.
-- A natural deduction proof of this can be seen in 3.4.3.jpg.
example (h: ¬(p ∧ q)): ¬p ∨ ¬q :=
  or.elim (em p)
    (assume hp: p, -- First column in the picture proof.
      show ¬p ∨ ¬q, from
      have hnq: ¬ q, from
        assume hq: q,
        show false, from h (and.intro hp hq),
      show ¬p ∨ ¬q, from or.inr hnq)
    (assume hnp: ¬ p, -- Second column in the picture proof.
      show ¬p ∨ ¬q, from or.inl hnp)