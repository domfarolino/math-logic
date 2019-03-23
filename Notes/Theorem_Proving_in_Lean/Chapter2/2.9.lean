-- 2.8 Implicit Arguments

-- Assume we have an implementation of our list below:

namespace hidden

universe u
constant list: Type u → Type u

constant cons: Π α: Type u, α → list α → list α
constant null: Π α: Type u, list α
constant append: Π α: Type u, list α → list α → list α

-- Given some type α, we can create lists and manipulate them.
variables l1 l2: list Prop
variable prop_var: Prop

#check cons Prop prop_var l1                  -- prop_var + l1
#check append Prop l1 l2                      -- l1 + l2
#check cons Prop prop_var (append Prop l1 l2) -- prop_var + (l1 + l2)

-- Note how in the last `#check` above, always passing Prop every time
-- top each list function to denote the type of list you're dealing with
-- is pretty redundant. This is because these functions ("constructors",
-- as the book calls them), are polymorphic over types, so we have to
-- repeatedly tell the function what type we're dealing with.

-- From the third example above, ideally Lean would be able to infer the
-- type "Prop" in both cases it appears:
--   1. Inference is possible in the first case, because the type
--      prop_var is Prop, and we should only be "cons"ing variables of
--      some type to a list of the same type
--   2. Inference is possible in the second case, because at this point
--      in time, we're expecting a list of type Prop (context).

-- "This is a central feature of dependent type theory: terms carry a
-- lot of information, and often some of that information can be inferred
-- from the context".

#check cons _ prop_var l1 -- The "_" tells lean to infer the type.
#check append _ l1 l2
#check cons _ prop_var (append _ l1 l2)

-- This is still a pain in the arse. When we have a parameter that can
-- generally be inferred, we can indicate to Lean that it should by
-- default be left implicit, by wrapping it in braces:

constant cons': Π {α: Type u}, α → list α → list α
constant null': Π {α: Type u}, list α
constant append': Π {α: Type u}, list α → list α → list α

#check cons' prop_var l1                  -- prop_var + l1
#check append' l1 l2                      -- l1 + l2
#check cons' prop_var (append' l1 l2) -- prop_var + (l1 + l2)

-- The above constants, and corresponding usages, are much cleaner.

end hidden