-- Assignment 4
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

-- Exercise 1
section
  variable A: Type
  variable f: A → A
  variable P: A → Prop
  variable h: ∀ x, P x → P (f x)

  -- Show the following:
  -- Scope of ∀ is maximal.
  example: ∀ y, P y → P (f (f y)) :=
    assume z: A, -- Arbitrary value |z| of type |A|.
    assume h2: P z,
    have h3: P (f z), from (h z) h2, -- Regular implication elimination.
    show P (f (f z)), from (h (f z)) h3 -- Re-apply |h|.
end

-- Exercise 2
section
  variable U: Type
  variables A B: U → Prop

  example: (∀ x, A x ∧ B x) → ∀ x, A x :=
    assume h1: (∀ x, A x ∧ B x),
    show ∀ x, A x, from
    assume z: U, -- Arbitrary |x| placeholder of type |U|.
    show A z, from and.left (h1 z) -- This is our ∀-introduction.
end

-- Exercise 3
section
  variable U: Type
  variables A B C: U → Prop

  variable h1: ∀ x, A x ∨ B x
  variable h2: ∀ x, A x → C x
  variable h3: ∀ x, B x → C x

  example: ∀ x, C x :=
    assume z: U,
    show C z, from
    or.elim (h1 z)
      (assume h4: A z, -- Assumption #1 from or-elimination.
      show C z, from h2 z h4)
      (assume h4: B z, -- Assumption #2 from or-elimination.
      show C z, from h3 z h4)
end

-- Exercise 4
open classical -- not needed, but you can use it

-- This is an exercise from Chapter 4. Use it as an axiom here.
axiom not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P)

example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
not_iff_not_self Q

section
  variable Person: Type
  variable shaves: Person → Person → Prop

  variable barber: Person
  variable h: ∀ x, shaves barber x ↔ ¬ shaves x x

  -- Show the following:
  example: false :=
    show false, from -- Redundant, I realize.
    have h1: shaves barber barber ↔ ¬ shaves barber barber, from h barber,
    show false, from (not_iff_not_self (shaves barber barber)) h1
end