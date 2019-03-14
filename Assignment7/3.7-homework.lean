-- Assignment 7
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

-- Exercise 1
namespace exercise1
  open classical
  variable A : Prop

  theorem dne (h: ¬¬ A) : A :=
    by_contradiction
    (assume h1 : ¬ A,
    show false, from h h1)

  example : A ∨ ¬ A :=
    have h1: ¬ (¬ (A ∨ ¬ A)), from
    -- Just proving h1.
    assume h2: (¬ (A ∨ ¬ A)),
    show false, from
    have h4: ¬ A, from
    assume ha: A,
    show false, from
    h2 (or.inl ha),
    have h3: (A ∨ ¬ A), from or.inr h4,
    show false, from h2 h3,

    show A ∨ ¬ A, from (dne (A ∨ ¬ A)) h1
end exercise1

-- Exercise 2
namespace exercise2
  variable P : Prop

  example : ¬ (P ↔ ¬ P) :=
    assume h1: (P ↔ ¬ P),
    have hNotP: ¬ P, from
      assume hp: P,
      have hNotP2: ¬ P, from (iff.elim_left h1) hp,
      show false, from hNotP2 hp,
    have hp: P, from (iff.elim_right h1) hNotP,
    show false, from hNotP hp
end exercise2