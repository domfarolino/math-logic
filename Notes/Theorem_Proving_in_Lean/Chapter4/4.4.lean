-- 4.4 The Existential Quantifier

-- See

open nat

example: ∃ x : ℕ, x > 0 :=
  have h: 1 > 0, from zero_lt_succ 0,
  exists.intro 1 h

theorem dom (x: ℕ) (h: x > 27): ∃ y, y < x :=
  exists.intro 27 h

example (x y z: ℕ) (hxy: x < y) (hyz: y < z): ∃ w, x < w ∧ w < z :=
  exists.intro y (and.intro hxy hyz)

#check @exists.intro

-------------------------------------------

variables (α: Type) (p q: α → Prop)

-- We eliminate the ∃ quantifier, operate on the "inner" part, and then
-- re-introduce the ∃ quantifier.
example (h: ∃ x, p x ∧ q x): ∃ x, q x ∧ p x :=
  exists.elim h
    (assume t,
      assume ht: p t ∧ q t,
      show ∃ x, q x ∧ p x, from
      exists.intro t (and.intro ht.right ht.left)
    )