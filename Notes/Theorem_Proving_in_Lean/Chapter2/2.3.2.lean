-- 2.3 Function Abstraction and Evaluation ...continued

-- So far we've only seen how to #check the type of functions,
-- and the type of their evaluations, when applied to some
-- expression. But...what about the value? Well, we can use
-- #reduce.

constants α β γ: Type

constant f: α → β
constant g: β → β → γ
constant h: α → α

constants (a: α) (b: β)

#check fun (a: α), a      -- Of type: α → α
#check (fun (a: α), a) a  -- Of type: α

-- Wait for it...
#reduce (fun (x: α), x) a -- Value: a. Woo!

-- Another...
#check (fun (x: α) (y: β), g (f x) y) -- α → β → γ

-- Since we're applying the function on `a b` variables, the type
-- we get back should be γ.
#check (fun (x: α) (y: β), g (f x) y) a b

-- And more specifically, the value should be the function invocations
-- with the specific variables we've given:
#reduce (fun (x: α) (y: β), g (f x) y) a b

-------------------------------------------------------

constants m n: ℕ

#check (m, n).1  -- ℕ.
#reduce (m, n).1 -- m.

-- The important bit about all of this is that every term in dependent
-- type theory supports the notion of reduction, or
-- normalization. This reduction is essentially "carrying out all the
-- computational reductions sanctioned by the underlying logic".