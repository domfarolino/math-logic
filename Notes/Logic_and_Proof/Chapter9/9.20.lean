-- 9.2 Using the universal quantifier

import init.data.nat
open nat

constant A : ℕ → Prop
constant B : ℕ → Prop

#check ∀ x, (A x ∨ B x) ∧ ¬ (A x ∧ B x)

-- Remember, after ∀ x, ___, the universal quantifier has the widest scope
-- possible. This means that:
#check ∀ x, A x -> B x

-- Is the same as:
#check ∀ x, (A x -> B x)

-- But we can tighten the bounds if we want:
#check ∀ x, (A x) -> B x

-- ∀-Introduction.
-- In this case, our goal is to _prove_ some ∀ statement. We do this with the
-- ∀-introduction.

example: ∀ x, A x :=
  show ∀ x, A x, from
  assume x, -- This just says "fix an arbitrary x of type ℕ" (in this case).
            -- We can also change the variable name here, since it is bound (I guess).
  show A x, from sorry -- sorry should be some proof of |A x|.

-- ∀-Elimination.
-- In this case, our goal is to prove some |A x|, from an |∀ x, A x| assumption.

-- Setup a variable of type |ℕ|, and |Type|
variable n: ℕ
variable z: Type

-- Setup a |C|, analogous to |A|, but which accepts Type, instead of |ℕ|.
-- constant A : ℕ → Prop
variable C: Type -> Prop

-- Setup hypotheses that ∀ x, we assume |A x| and |C x| are true. We are allowed
-- to "apply" this hypotheses to any variable whose type matches the formula
-- associated with the hypothesis.
variable h1: ∀ x, A x -- Can apply this to arbitrary values of |ℕ|.
variable h2: ∀ x, C x -- Can   |     |   |     |        |   |  |Type|.

example: A n :=
  show A n, from h1 n

example: C z :=
  show C z, from h2 z