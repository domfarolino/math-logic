-- 4.40 Forward Reasoning
-- Lean provides the "have" command for forward reasoning.

variables A B C : Prop

variable h1: A -> B
variable h2: B -> C

-- Traditionally we might prove A -> C, as:
example: A -> C :=
assume h, -- Implicitly, |h| is a proof of |A|.
show C, from h2 (h1 h)

-- However we can use "have", like this:

example: A -> C :=
assume h: A,
have h3: B, from h1 h, -- Build up a proof of B now (forward) now.
show C, from h2 h3