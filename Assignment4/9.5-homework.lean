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
  variable U : Type
  variables A B : U → Prop

  example : (∀ x, A x ∧ B x) → ∀ x, A x :=
    assume h1: ∀ x, A x ∧ B x,
    assume z, -- Arbitrary value |z|, of type |A|, like exercise 1.
    have h2: A(z) ∧ B(z), from h1 z, -- Sometimes using parens looks nicer to me.
    show A z, from and.left h2 -- This is our ∀-introduction.
end

-- Exercise 3
section
  -- Setup some variables & hypotheses.
  variable U : Type
  variables A B C : U → Prop
  variable h1 : ∀ x, (A x ∨ B x)
  variable h2 : ∀ x, (A x → C x)
  variable h3 : ∀ x, (B x → C x)

  example : ∀ x, C x :=
    assume y, -- Arbitrary value |z|, of type |U|.
    have h4: A(y) ∨ B(y), from h1 y, -- ∀-elimination on |h1|.
    have h5: A(y) → C(y), from h2 y, -- ∀-elimination on |h2|.
    have h6: B(y) → C(y), from h3 y, -- ∀-elimination on |h3|.
    show C y, from
    or.elim h4
      (assume h8 : A(y), -- Assumption #1 from or-elimination.
        show C y, from h5 h8)
      (assume h9 : B y,  -- Assumption #2 from or-elimination.
        show C y, from h6 h9)
end

-- Exercise 4
-- This is an exercise from Chapter 4. Use it as an axiom here.
axiom not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P)
example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
not_iff_not_self Q

section
  variable Person : Type
  variable shaves : Person → Person → Prop
  variable barber : Person
  variable h : ∀ x, shaves barber x ↔ ¬ shaves x x

  -- Show the following:
  example : false :=
    have h1 : (shaves barber barber) ↔ ¬ (shaves barber barber), from h barber,
    show false, from (not_iff_not_self (shaves barber barber)) h1
end