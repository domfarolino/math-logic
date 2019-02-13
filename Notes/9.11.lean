-- 9.1 ...continued

#check nat -- This represents the natural numbers.
#check ℕ   -- Same as above.

-- Can use this to prevent name collisions.
namespace hidden

-- Define our terms.
constant mul: ℕ -> ℕ -> ℕ
constant add: ℕ -> ℕ -> ℕ
constant square: ℕ -> ℕ

-- Define some formulas.
constant even: ℕ -> Prop
constant odd: ℕ -> Prop
constant prime: ℕ -> Prop
constant divides: ℕ -> ℕ -> Prop
constant lt: ℕ -> ℕ -> Prop -- Less-than
constant zero: ℕ
constant one: ℕ -- So...I guess these don't have "values"?

variables w x y z: ℕ

-- If we were outside of the namespace |hidden|, we'd have to prefix hidden's
-- members with |hidden.| before using them, as follows:
#check hidden.mul x y
#check hidden.odd hidden.zero
#check hidden.prime (hidden.add x y)
-- Clearly this works OK in the namespace as well.

------------------------------------
-- "We can even declare infix notation of binary operations and relations".

-- These essentially bind some previously-defined constant
infix + := hidden.add
infix * := mul
infix < := lt

-- For some reason I can't figure out how to use the infix notation.
#check add x y
#check add x (add y z)
#check even (add x (add y z)) /\ prime (square z)

end hidden