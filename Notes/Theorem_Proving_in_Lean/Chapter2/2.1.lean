-- 2.1 Simple Type Theory

constants m n: nat

constant f: ℕ → ℕ -- Function mapping natural nums → natural nums.

-- Function mapping a ℕ to a function that maps ℕs to ℕs.
constant g: ℕ → ℕ → ℕ

-- Defines the type of cartesian product of (ℕ, ℕ).
constant p: ℕ × ℕ

-- Example checks.
#check f (p.1)
#check f (p.2)

#check f (p.fst)
#check f (p.snd)

#check (m, n) -- Produces a cartesian product.
#check (g p.1) p.2
#check g p.1 p.2 -- Just another way to write the above.

-- Functions like |g| are useful because having them return another
-- function, instead of forcing us to apply two arguments "g(a, b)" right
-- away allows us to partially apply |g|. Put differently, the fact that
-- |g| returns a function of type ℕ → ℕ allows us to apply arguments to
-- |g| one at a time. This is a very common concept in functional
-- programming.

-- You might realize the same kind of function can be written to take
-- all or both of its arguments at once:

constant c: ℕ × ℕ → ℕ
#check c (m, n)

-- The process of redefining |c| to look like |g| is called currying,
-- which as stated above, is a very common functional paradigm.