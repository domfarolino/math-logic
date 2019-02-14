-- Assignment 4
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

-- Exercise 1
-- I've changed |f| to |fn| and |P| to |Prime| just to make it a little more
-- relatable on first consumption; the semantics are unchanged.
section
  variable A : Type
  variable fn : A → A
  variable Prime : A → Prop

  -- This is a given hypothesis:
  variable h : ∀ x, Prime x → Prime (fn x)

  -- Show the following:
  example : ∀ y, Prime y → Prime (fn y) :=
    assume z, -- Arbitrary value |z|, of type |A|.
    show Prime z → Prime (fn z), from (h z)
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