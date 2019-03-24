-- Assignment 8
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

-- For this assignment, proofs of all of the 11 given identities in
-- section 4.4 are presented here.

open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r :=
  assume h: (∃ x : α, r),
  exists.elim h
  (assume t: α,
    assume ht: r,
    show r, from ht
  )

example: r → (∃ x : α, r) :=
  assume hr: r,
  show (∃ x : α, r), from exists.intro a hr

example: (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  iff.intro
    (assume h: (∃ x, p x ∧ r),
      show (∃ x, p x) ∧ r, from
      exists.elim h
        (assume y: α,
          assume hinner: p y ∧ r,
          have hey: ∃ y, p y, from exists.intro y hinner.left,
          show (∃ y, p y) ∧ r, from and.intro hey hinner.right
        )
    )
    (assume h: (∃ x, p x) ∧ r,
      show (∃ x, p x ∧ r), from
      exists.elim h.left
      (assume y: α,
        assume hinner: p y,
        have hand: p y ∧ r, from (and.intro hinner h.right),
        show (∃ y, p y ∧ r), from exists.intro y hand
      )
    )

example: (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  iff.intro
    (assume h: (∃ x, p x ∨ q x),
      show (∃ x, p x) ∨ (∃ x, q x), from
      exists.elim h
      (assume y: α,
        assume hinner: p y ∨ q y, show (∃ y, p y) ∨ (∃ y, q y), from
        or.elim hinner
          (assume hpy: p y,
            have halmost: (∃ y, p y), from exists.intro y hpy,
            show (∃ y, p y) ∨ (∃ y, q y), from or.inl halmost
          )
          (assume hqy: q y,
            have halmost: (∃ y, q y), from exists.intro y hqy,
            show (∃ y, p y) ∨ (∃ y, q y), from or.inr halmost
          )
      )
    )
    (assume h: (∃ x, p x) ∨ (∃ x, q x),
      show (∃ x, p x ∨ q x), from
      or.elim h
        (assume h1: (∃ x, p x),
          exists.elim h1
            (assume y: α,
              assume hinner: p y,
              have halmost: p y ∨ q y, from or.inl hinner,
              show (∃ x, p x ∨ q x), from exists.intro y halmost
            )
        )
        (assume h1: (∃ x, q x),
          exists.elim h1
            (assume y: α,
              assume hinner: q y,
              have halmost: p y ∨ q y, from or.inr hinner,
              show (∃ x, p x ∨ q x), from exists.intro y halmost
            )
        )
    )

example: (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  iff.intro
    (assume h: (∀ x, p x),
      show ¬ (∃ x, ¬ p x), from
      assume hpos: (∃ x, ¬ p x),
      show false, from
      exists.elim hpos
        (assume y: α,
          assume hinner: ¬ p y,
          show false, from hinner (h y)
        )
    )
    (assume h: ¬ (∃ x, ¬ p x),
      show (∀ x, p x), from
      assume x: α,
      show p x, from
      by_contradiction
        (assume h1: ¬ p x,
          have hpos: ∃ x, ¬ p x, from exists.intro x h1,
          show false, from h hpos
        )
      -- Originally went with this, but I found this was not the right
      -- approach:
      -- by_contradiction (assume h1: ¬ (∀ x, p x), sorry)
    )

-- This one was rough...
example: (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  iff.intro
    (assume h: (∃ x, p x),
      show ¬ (∀ x, ¬ p x), from
      assume hpos: (∀ x, ¬ p x),
      show false, from
      exists.elim h
        (assume y: α,
          assume hinner: p y,
          show false, from (hpos y) hinner
        )
    )
    (assume h: ¬ (∀ x, ¬ p x),
      show (∃ x, p x), from
        by_contradiction
          (assume hneg: ¬ (∃ x, p x),
            have hpos: (∀ x, ¬ p x), from
              assume y: α,
              -- have hnpy: ¬ p y, from -- Can uncomment this and "hnpy," below if wanted.
                assume hy: p y,
                  have hey: ∃ y, p y, from exists.intro y hy,
                  show false, from hneg hey,
              -- hnpy,
            show false, from h hpos
          )
    )

example: (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  iff.intro
    (assume h: (¬ ∃ x, p x),
      show (∀ x, ¬ p x), from
      assume x: α,
      show ¬ p x, from
      assume hpx: p x,
      show false, from h (exists.intro x hpx)
    )
    (assume h: (∀ x, ¬ p x),
      show (¬ ∃ x, p x), from
      assume hpos: ∃ x, p x,
      show false, from
      exists.elim hpos
        (assume y: α,
          assume hpy: p y,
          show false, from (h y) hpy
        )
    )

example: (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  iff.intro
    (assume h: (¬ ∀ x, p x),
      show (∃ x, ¬ p x), from
      by_contradiction
        (assume hneg: ¬ (∃ x, ¬ p x),
          have hpos: (∀ x, p x), from
            assume y: α,
            -- have hpy: p y, from -- Can uncomment this and "hpy," if wanted.
            by_contradiction
              (assume hnpy: ¬ p y,
                show false, from hneg (exists.intro y hnpy)
              ),
            -- hpy,
          show false, from h hpos
        )
    )
    (assume h: (∃ x, ¬ p x),
      show (¬ ∀ x, p x), from
      assume hpos: (∀ x, p x),
      show false, from
      exists.elim h
        (assume y: α,
          assume hinner: ¬ p y,
          show false, from hinner (hpos y)
        )
    )

-- Last 3:
example: (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  iff.intro
    (assume h: (∀ x, p x → r),
      show (∃ x, p x) → r, from
      assume hex: (∃ x, p x),
      show r, from
      exists.elim hex
        (assume y: α,
          assume hinner: p y,
          show r, from h y hinner)
    )
    (assume h: (∃ x, p x) → r,
      show (∀ x, p x → r), from
      by_cases
        (assume hep: ∃ x, p x,
          show (∀ x, p x → r), from
          assume x, -- Does not specifically have to be x.
          fun h', h hep
        )
        (assume hnep : ¬ ∃ x, p x,
          -- show (∀ x, p x → r), from
          by_contradiction
            (assume hnap: ¬ (∀ x, p x → r),
              have hep: ∃ x, p x, from
              by_contradiction
                (assume hnep': ¬ ∃ x, p x,
                  have hap: (∀ x, p x → r), from
                    assume x: α,
                    show p x → r, from
                      (assume hpx: p x,
                        show r, from absurd (exists.intro x hpx) hnep'
                      ),
                  show false, from hnap hap
                ),

              show false, from hnep hep
            )
        )
    )

-- Given by the book:
example: (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  iff.intro
  (assume ⟨b, (hb : p b → r)⟩,
    assume h2 : ∀ x, p x,
    show r, from  hb (h2 b))
  (assume h1 : (∀ x, p x) → r,
    show ∃ x, p x → r, from
      by_cases
        (assume hap : ∀ x, p x,
          show ∃ x, p x → r, from
          ⟨a, fun h', h1 hap⟩
        )
        (assume hnap : ¬ ∀ x, p x,
          by_contradiction
            (assume hnex : ¬ ∃ x, p x → r,
              have hap : ∀ x, p x, from
                assume x,
                by_contradiction
                  (assume hnp : ¬ p x,
                    have hex : ∃ x, p x → r,
                      -- from ⟨x, (assume hp, absurd hp hnp)⟩,
                      from exists.intro x (assume hp: p x, absurd hp hnp),
                    show false, from hnex hex),
              show false, from hnap hap)))

example: (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  iff.intro
    (assume h: (∃ x, r → p x),
      assume hr: r,
      show ∃ x, p x, from
      exists.elim h
        (assume y: α,
          assume hinner: r → p y,
          have hpy: p y, from hinner hr,
          exists.intro y hpy
        )
    )
    (assume h: (r → ∃ x, p x),
      show (∃ x, r → p x), from
      by_cases
        (assume hc: r,
          exists.elim (h hc)
          (assume y: α,
            assume hinner: p y,
            have hcom: r → p y, from (assume hr, hinner),
            show (∃ x, r → p x), from exists.intro y hcom
          )
        )
        (assume hc: ¬ r,
          show (∃ x, r → p x), from
            exists.intro a (assume hr: r, absurd hr hc) -- Weird.
        )
    )