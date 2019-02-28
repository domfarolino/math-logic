-- So far we've seen things like:
--   - How to prove (¬ B ∧ A) from the premise (A ∧ ¬ B)
--   - How to apply one hypothesis to another that contains an implication
--
--  What we haven't quite seen yet is how to do an implication introduction
-- ourselves. We can do this with the "assume" or lambda syntax. Consider
-- "We can instead obtain a proof of A ∧ ¬ B → ¬ B ∧ A as follows:"

variables A B: Prop

#check assume h: A /\ not B, and.intro (and.right h) (and.left h)

-- This performs an implication introduction, which can cancel a hypothesis.
-- Consider the even simpler proof of A → A ∧ A.

-- variable A : Prop -- (not needed)

#check assume h : A, and.intro h h