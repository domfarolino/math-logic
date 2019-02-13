-- 9.1 ...continued

-- Actually, some of the terms and formulas from the last program are built-in
-- Lean under the `init.data.nat` library(?).
import init.data.nat
open nat
-- Now we have basic infix operations available to us.

constant square: ℕ -> ℕ
constant add: ℕ -> ℕ -> ℕ

constant even: ℕ -> Prop
constant odd: ℕ -> Prop
constant lt: ℕ -> ℕ -> Prop

variables w x y z: ℕ

#check even(square(y)) /\ odd(square(z))
#check even (add x y) \/ even (x * y)
#check x < y /\ even(x)
#check (lt x y) /\ even(x) -> odd(square(z) + y)