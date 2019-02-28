-- Simple proof of A /\ A, with a variable, and hypothesis assumption.

variable A: Prop

-- See how instead of explicitly writing the assumption |h1| as a variable, we
-- can still create this hypothesis on the fly when we need it via 'assume'.
-- We put a comma after the localized hypothesis, and we can refer to it later.
#check (assume h1: A, and.intro h1 h1)

-- Also note that assume == λ (fun, in ascii).
#check (fun h1: A, and.intro h1 h1)