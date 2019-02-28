-- 9.1 Functions, Predicates, and Relations

-- In these specific examples, |constant| can be replaced with |variable|.
-- This interchangeability is not always the case though, as |constant|s are a
-- little more powerful than |variable|s, since they add a new object to Lean
-- essentially, they can be referenced elsewhere.
constant U: Type

constant c: U              -- Constant symbol.
constant f: U -> U         -- Unary function symbol.
constant g: U -> U -> U    -- Binary function symbol.
constant P: U -> Prop      -- Unary relation symbol.
constant R: U -> U -> Prop -- Binary relation symbol.

-- Define variables to actually use with the above symbols.
variables x y : U

-- These all resolve to type `U`; as such, they can be considered "terms" in
-- FOL.
#check c
#check f c
#check g x c
#check g x (f c)
#check g c (f x)

-- These all resolve to type `Prop`; as such, they can be considered "formulas".s
-- Example: even(), odd(), etc.
#check P x
#check P (g x y)
#check R x c
#check R x y