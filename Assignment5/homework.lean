-- Exercise 5
section
  variable U: Type
  variables A B: U → Prop

  example : (∃ x, A x) → ∃ x, A x ∨ B x := -- Added parens for clarity.
    assume h1: (∃ x, A x),
    -- Need to do exists elimination, to get A y alone.
    show ∃ x, (A x ∨ B x), from
    exists.elim h1 (
      assume y: U,
      assume h2: A y,
      have h3: A y ∨ B y, from or.inl h2,
      show ∃ x, (A x ∨ B x), from exists.intro y h3
    )
end

-- Exercise 6
section
  variable U: Type
  variables A B: U → Prop

  variable h1: ∀ x, A x → B x
  variable h2: ∃ x, A x

  example: ∃ x, B x :=
    show ∃ x, B x, from
    exists.elim h2 ( -- We know we need a variable to apply |h1| to, and we can
      assume y: U,   -- get that variable via assumption by doing exists.elim.
      assume h3: A y, -- Just usual exists.elim assumptions going on here...
      have h4: A y -> B y, from h1 y,
      have h5: B y, from h4 h3, -- Implication elimination.
      show ∃ x, B x, from exists.intro y h5
    )
end

-- Exercise 7
section
  variable U: Type
  variables A B C: U → Prop

  variable h1: ∃ x, A x ∧ B x
  variable h2: ∀ x, B x → C x

  example: ∃ x, (A x ∧ C x) := -- Added parens for clarity.
    show ∃ x, (A x ∧ C x), from
    exists.elim h1 (
      assume y: U,
      assume h3: A(y) ∧ B(y),
      have h4: C(y), from (h2 y) (and.right h3), -- Both ∀, and implication elimination.
      show ∃ x, (A x ∧ C x), from
      exists.intro y (and.intro (and.left h3) h4) -- Sorry not sorry.
      -- OK, so that last line can also be written as:
      -- have h5: A y ∧ C y, from and.intro (and.left h3) h4,
      -- exists.intro y h5
    )
end

-- Exercise 8
-- These proofs are the same as Notes/Chapter8/8.5.1.JPG.
section
  variable U: Type
  variables A B C: U → Prop

  example : (¬ ∃ x, A x) → ∀ x, ¬ A x :=
    assume h1: ¬ (∃ x, A x),
    assume y: U, -- ∀-introduction (see 9.2.1); business as usual.
    show ¬ (A y), from
    assume h2: A y, -- Can assume this from negation.
    have h3: (∃ x, A x), from exists.intro y h2,
    show false, from h1 h3

  example : (∀ x, ¬ A x) → ¬ ∃ x, A x :=
    assume h1: (∀ x, ¬ A x),
    assume h2: ∃ x, A x,
    show false, from
    exists.elim h2 (
      assume y: U,
      assume h3: A(y),
      show false, from (h1 y) h3 -- Beautiful.
    )
end

-- Exercise 9
section
  variable U: Type
  variables R: U → U → Prop

  example: (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y :=
    assume h1: ∃ x, (∀ y, R x y), -- Re-arrange parens for clarity.
    show ∀ y, ∃ x, (R x y), from
    assume b: U,
    show ∃ x, (R x b), from
    exists.elim h1 (
      assume a: U, -- Get to assume this and next line, bc ∃-elim.
      assume h2: ∀ y, R a y,
      have h3: R a b, from h2 b,
      show ∃ a, (R a b), from exists.intro a h3
    )
end