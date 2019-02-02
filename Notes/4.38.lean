-- 4.38 Examples
-- Prove (A -> B) /\ (B -> C) -> (A -> C)

variables A B C: Prop

variable h1: A -> B
variable h2: B -> C

example: A -> C :=
assume h: A,
show C, from h2 (h1 h)