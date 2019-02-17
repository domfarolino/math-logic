-- 9.3 Using the existential quantifier

import init.data.nat
open nat

variable U : Type
variables A B : U → Prop

variable y: U
variable h: A(y)

-- ∃-introduction.
example: ∃ x, A x :=
  exists.intro y h

-- You can see that we require some free variable |x|, such that some |A x| is
-- true. Then we simply |exists.intro| on the variable, and the proof of |A x|.

-- ∃-elimination.
-- The elimination rule follows directly from natural deduction. If we are
-- trying to prove |C|, from ∃ x, A(x), we introduce a new variable |y|, assume
-- |A(y)|, and prove |Q| from the assumption |A(y)|.

variable Q: Prop
variable h1: ∃ x, A(x)
variable h2: ∀ b, A(b) -> Q

-- See 9.30.jpg for the next two examples:

example: Q :=
  show Q, from
  exists.elim h1 ( -- Want to prove |Q|, from |h1|.
    assume y: U,   -- Assume a variable of type |U| (because A in |h1| operates on this).
    assume h3: A(y), -- Assume A(y), for |h1|.
    have h4: A(y) -> Q, from h2 y, -- ∀-elimination, by applying |h2| to our variable.
    show Q, from h4 h3 -- Regular implication elimination.
  )

-- Here's another example that uses both ∃-{intro, elim}

example : (∃ x, A(x) ∧ B(x)) → ∃ x, A(x) :=
  assume h1: (∃ x, A(x) ∧ B(x)),
  show ∃ x, A(x), from
  exists.elim h1 (
    assume y: U,
    assume h2: A(y)∧B(y),
    have h3: A(y), from and.left h2,
    show ∃ x, A(x), from exists.intro y h3
  )

-- And another! SEe 9.30-2.jpg for this example:

example : (∃ x, A x ∨ B x) → (∃ x, A x) ∨ (∃ x, B x) :=
  assume h1: (∃ x, A x ∨ B x),
  show (∃ x, A x) ∨ (∃ x, B x), from
  exists.elim h1 (
    assume y: U, -- This is important, and easy to forget in exists.elim.
    assume h2: A(y) ∨ B(y),
    show (∃ x, A x) ∨ (∃ x, B x), from
    or.elim h2
      (assume h3: A(y),
      show (∃ x, A x) ∨ (∃ x, B x), from
      have h4: (∃ x, A(x)), from exists.intro y h3,
      or.inl h4)
      (assume h3: B(y),
      show (∃ x, A x) ∨ (∃ x, B x), from
      have h4: (∃ x, B (x)), from exists.intro y h3,
      or.inr h4)
  )

-- Below is an example proof we did in ND, from Chapter 8:

example : (∀ x, A x → ¬ B x) → ¬ ∃ x, A x ∧ B x :=
  assume h1: (∀ x, A x → ¬ B x),
  assume h2: ∃ x, A x ∧ B x,
  show false, from
  exists.elim h2 (
    assume y: U,
    assume h3: A(y) ∧ B(y),
    have h4: A(y) → ¬ B(y), from h1 y,
    have h5: B(y), from and.right h3,
    show false, from (h4 (and.left h3)) h5
  )