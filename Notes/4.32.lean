-- Building Natural Deduction Proofs
-- 4.32 Conjunction

variables A B: Prop

-- We implement and-introduction with and.intro.
variable h1: A
variable h2: B

-- We implement and-elimination rules with and.left and and.right.

variable h3: A /\ B
example: A := show A, from and.left h3
example: B := show B, from and.right h3