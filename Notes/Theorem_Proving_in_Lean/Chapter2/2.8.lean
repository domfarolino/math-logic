-- 2.8 Dependent Types

-- The short explanation of what makes dependent type theory "dependent",
-- is that types can depend on parameters. For example, with list:

constant α: Type 0

#check list
#check list α
#check list ℕ
#check list bool
#check list Prop
#check list (Type 1)

-- The type `list α` depends on the parameter α. Another perhaps more
-- clear example is the function `cons`. We expect `cons` to be
-- polymorphic, i.e., work on any "type". It makes sense then, to have
-- the first argument to `cons`, be the type that it is working on.
-- "In other words, for ever α, cons α is the function that takes an
-- element a: α and a list l: list α, and returns a new list, so we
-- have `cons α a l`: list α".

-- Obviously `cons α` should have type `(α → list α) → list α`, since
-- the first concrete parameter should be some a: α to add to the second
-- parameter, a list `list α`. The result is a list. But what type should
-- just plain old `cons` have?

-- Since the parameter/argument types of `cons` are dependent on the
-- given type, we're experiencing a "Pi type", or "dependent function
-- type".

constant x: α
constant β: α → Type

constant Bn: ℕ → Type

def dep_type (x: α) : Type := β x -- Just a pass-through for β.

-- Checks and reduces for dep_type.
#check Π x: α, β x -- Just Type. Not α → Type.
#check dep_type -- Just a pass-through for β.
#check dep_type x -- Type.
#reduce dep_type x -- Reduces to (β x), not further-reducible.

-- As you can see, the type `Π x: α, β x` is not the same as the function
-- dep_type. Π x is a type dependent on its input (which is not really
-- a traditional "input" it seems? Not sure, this is kinda confusing). It
-- seems that the Pi type is an atomic type (not a function) that depends
-- on what is basically invisible input.

-- `α → β` is just notation for Π x: α, β, when β does not depend on x.
-- When β does depend on x, `Π x: α, β` denotes a dependent function
-- type.

namespace hidden

  universe u
  constant list: Type u → Type u

  constant cons: Π type: Type u, type → list type → list type

  constant prop_to_add: Prop
  constant list_of_props: list Prop

  #check cons
  #check cons Prop                           -- First takes a type.
  #check cons Prop prop_to_add               -- Then takes an element
  #check cons Prop prop_to_add list_of_props -- Then takes a list.

end hidden

-- A similar thing goes for vec operations.

namespace vector

  universe u
  -- A vector is defined by a type and a length.
  constant vec: Type u → ℕ → Type u

  constant empty: Π α: Type u, vec α 0
  constant cons: Π (α: Type u) (n: ℕ), α → vec α n → vec α (n + 1)
  constant append_vecs: Π (α: Type u) (m: ℕ) (n: ℕ),
    vec α m → vec α n → vec α (m + n)
end vector

-- This might be confusing and abstract, but at the very least, you can
-- think of it like this: When you have a function whose parameter/return
-- types all depend on a given type, you'll want:
--   1. The first parameter to be a "type"
--   2. The rest of the types to "depend" on the type that was passed in
--      as the first parameter.
-- In this case, you'll use a dependent function type, or a Π type, of
-- the form Π (x: Type u), where x is the type that our other types
-- described in (2) can depend on.