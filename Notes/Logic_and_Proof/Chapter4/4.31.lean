-- Building Natural Deduction Proofs
-- 4.31 Implication

variables A B: Prop

-- Implication introduction (by "assume" keyword).
example: A /\ B -> B /\ A :=
assume h: A /\ B,
show B /\ A, from and.intro (and.right h) (and.left h)

-- (or another example); I actually do not know if this is a legitimate example.
variable ht: A -> B

example : A → B :=
assume h : A,
show B, from ht h
--

-- Implication elimination (by hypothesis application).
variable h1: A -> B
variable h2: A
example: B := show B, from (h1 h2)