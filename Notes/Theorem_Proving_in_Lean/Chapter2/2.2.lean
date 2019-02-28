-- 2.2 Types as Objects

-- In Lean, types such as ℕ and bool are first-class objects as well,
-- meaning they must have a type.

#check ℕ -- Its type is: |Type|.

-- Therefore we can create our own types:

constant α: Type
constant f: Type → Type
constant g: Type → Type → Type

#check α
#check f α
#check f ℕ
#check g (f ℕ) α

-- Above, saying `constant α: Type` actually created a new type α or us.
-- We can use this type as follows:

constant m: α
constant alpha_only_fn: α → α
#check alpha_only_fn m

-- We cannot write, for example: `alpha_only_fn α`, because α is the
-- Type that the function accepts, therefore we cannot give it the
-- actual type itself, we have to give it something _of type_ α. This
-- is like doing the following:

-- #check bool && bool

-- The above commented out line does not work because `&&` is expecting
-- something of type |bool|, not the type itself. Bool is of type |Type|,
-- so technically there is a mismatch.

--------------------------------------------------------

-- Given any |Type| α, `list α` denotes a list of type α.

#check list ℕ
#check list α

-- What type is |Type|?

#check Type
#check Type 233

#check list (Type 233)

-- Lean has an infinite hierarchy of types, each expanding in magnitude!

constant DomType: Type 11
#check DomType -- A very powerful/general type, encapsulating Types 0-10.

#check list -- Output means that whenever the given argument has a type
            -- of Type n, the expression `list α` is also of type Type n.

#check list α -- It makes sense. α's type is |Type|, and so is `list α`.