-- 2.3 Function Abstraction and Evaluation

-- Given a cartesian pair of some types, we can "extract" the members
-- with `.fst` and `.snd`, or `.1` and `.2`, or even `fst var` and
-- `snd var`.

-- In this section we're going to learn how to create a function
-- from another expression, which is called "abstraction".

-- Creating anonymous functions:

-- This function, defined by the `fun` keyword, is nameless,
-- accepts a parameter named |x| of type |nat|, and returns |x + 1|.

constants α β: Type
constant a: α
constant b: β

constant p: α → β → bool

#check fun x: ℕ, x + 1 -- Simple anon fn.
#check fun x: α, p x   -- In: α; Out: β → bool; = α → β → bool.
#check fun (x: α) (y: β), p x y -- Basically just a pass-through for |p|.

#check fun x: α, p x b -- α → bool.

#check fun x: α, x -- Identity function on α.
#check fun x: α, β -- α → Type (0); Always returns a |Type|. Kinda weird.

-- Here is another example of a function that creates another function.
-- You can look at it as a function that takes in an argument of type
-- α, and returns a function that takes an argument of type β, and
-- immediately returns said last argument.
#check fun (x: α) (b: β), b -- α → β, equivalently written as:
#check fun (x: α), fun (b: β), b

-- I think this is really clear in the last rendition of it, since
-- it is more explicitly returning a function.

----------------------------------------------------------------------

-- We can actually apply lambda functions to variables/expressions:

#check (fun (x: α) (y: β), y) a b -- After applying to |a b|, we get
                                  -- the result of |y|, of type β.
