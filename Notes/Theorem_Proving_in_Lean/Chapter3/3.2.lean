-- 3.2 Working with Propositions as Types

constants p q: Prop

theorem t1: p → q → p := fun (hp: p), fun (hq: q), hp

-- This newly-introduced theorem is the same as the constant we defined
-- in the 3.1 notes, however in this case the arguments are of type Prop
-- instead of type Type (?).

-- Note that in the above, the function/lambda abstractions are
-- equivalent to temporary assumptions:

theorem t2: p → q → p :=
  assume hp: p,
  assume hq: q,
  show p, from hp

-- Lean also provides the word "lemma" as an alternate syntax to
-- "theorem". Furthermore, "axiom" is interchangeable with "constant".

-- It should be noted that `t1` is true for any propositions `p` and
-- `q`, so it would be better to define `t1` in such a way that
-- represents this quantification. We can do this the short-handed way
-- or the long-handed way, or even the more-explicit way.

theorem t3 (p q: Prop) (hp: p) (hq: q): p := hp
theorem t4: Π (p q: Prop), p → q → p :=
  fun (p q: Prop),
  fun (hp: p),
  fun (hq: q), hp
theorem t5: ∀ (p q: Prop), p → q → p :=
  fun (p q: Prop),
  fun (hp: p),
  fun (hq: q), hp

#check t3
#check t4
#check t5

theorem t56 (h: p ∧ q): p := and.left h