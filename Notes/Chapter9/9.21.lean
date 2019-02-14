-- 9.2 Using the universal quantifier ...continued

import init.data.nat
open nat

variable U : Type
variables A B : U → Prop

-- So we'll be using ∀-Introduction, since we are proving a universally
-- quantified statement, therefore we start with some baser assumption, and
-- introduce a ∀, to match the proof we need.
variable h1: ∀ x, A x → B x
variable h2: ∀ x, A x

example : ∀ x, B x :=
  assume y, -- Some |U| (|Type|). Can also be called |x|, it seems.
  show B y, from
  have h3: A y, from h2 y, -- Just like last file, where we apply an assumption
                           -- to an assumption whose type matches the formula's
                           -- input in the hypothesis.
  have h4: A y -> B y, from h1 y,
  -- show B y, from
  h4 h3

-- We can also do the above prove without |have| statements, of course.