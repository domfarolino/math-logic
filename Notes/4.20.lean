-- Introducing "example"
-- This tells lean that you are about to prove a theorem of a certain type.
-- It should be followed by the proof itself.

variables A B : Prop

example : A ∧ ¬ B → ¬ B ∧ A :=
assume h : A ∧ ¬ B,
and.intro (and.right h) (and.left h)

-- Lean will check the expression after ":=" to make sure it is of the right
-- type. Example actually lets us leave out some information in the actual
-- proof (for example, the hypothesis |h| can be inferred).