-- 3.6 Examples of Propositional Validities

open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (assume h: p ∧ q,
      show q ∧ p, from and.intro h.right h.left)
    (assume h: q ∧ p,
      show p ∧ q, from and.intro h.right h.left)

example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (assume h: p ∨ q,
      show q ∨ p, from
      or.elim h
        (assume hp: p, or.inr hp)
        (assume hq: q, or.inl hq)
    )
    (assume h: q ∨ p,
      show p ∨ q, from
      or.elim h
      (assume hq: q, or.inr hq)
      (assume hp: p, or.inl hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume h: (p ∧ q) ∧ r,
      show p ∧ (q ∧ r), from and.intro
        (h.left.left) -- p
        (and.intro h.left.right h.right)
    )
    (assume h: p ∧ (q ∧ r),
      show (p ∧ q) ∧ r, from and.intro
      (and.intro h.left h.right.left)
      (h.right.right)
    )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume h: (p ∨ q) ∨ r,
      show p ∨ (q ∨ r), from
      or.elim h
        (assume hpq: p ∨ q,
          or.elim hpq
            (assume hp: p, or.inl hp)
            (assume hq: q, or.inr (or.inl hq))
        )
        (assume hr: r, or.inr (or.inr hr))
    )
    (assume h: p ∨ (q ∨ r),
      show (p ∨ q) ∨ r, from
      or.elim h
        (assume hp: p, or.inl (or.inl hp))
        (assume hqr: q ∨ r,
          or.elim hqr
          (assume hq: q, or.inl (or.inr hq))
          (assume hr: r, or.inr hr)
        )
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : ¬(p ↔ ¬p) := sorry
example : (p → q) → (¬q → ¬p) := sorry

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry