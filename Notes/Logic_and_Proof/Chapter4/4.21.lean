-- Introducing "show"
-- "show" can let us provide more information than is _necessary_. It lets us
-- tell the lean parser what exactly we are intending to prove at each substep.

variables A B : Prop

example : A ∧ ¬ B → ¬ B ∧ A :=
assume h : A ∧ ¬ B,
show ¬ B ∧ A, from and.intro (and.right h) (and.left h)

-- For example, we'll be really explicit here:

example : A ∧ ¬ B → ¬ B ∧ A :=
assume h,
and.intro
  (show not B, from and.right h)
  (show     A, from and.left h)