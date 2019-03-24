-- 4 Quantifiers and Equality

-- 4.1 The Universal Quantifier

variable α: Type
variables p q: α → Prop

-- ∀ Introduction. To prove ∀ A x, we need to:
--   1. Assume an arbitrary |x|
--   2. Prove A x

example: (∀ x: α, p x ∧ q x) → ∀ y: α, p y :=
  assume h1: (∀ x: α, p x ∧ q x),
  show ∀ y: α, p y, from
  assume y: α, -- ∀ introduction.
  show p y, from (h1 y).left -- Applying a ∀ stmt to a variable removes
                             -- the ∀. It is ∀ elimination.

-- Transitive relation:
variable r: α → α → Prop
variable trans_r: ∀ x y z, r x y → r y z → r x z

variables a b c : α
variables (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc