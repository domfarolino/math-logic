universe u
-- 1.
#check implies

-- 2.
#check prod

-- 3.
#check fun {a: Type} (x y : a), y

-- 4.
#check Type

-- 5.
def double (x: ℕ): ℕ := x + x
def twice {a: Type u} (f: a → a) (g: a) := f (f g)
#check twice
#reduce twice twice double 2

-- 6.
def fourTimes {a: Type u}: (a → a) → a → a := twice twice
#reduce fourTimes double 2

-- 7.
def eightTimes: ℕ → ℕ := fourTimes double
#reduce eightTimes 2

-- 8.
-- Look at Assignment6.

-- 9.
variable A: Prop
section
  variable h1: A ↔ ¬ A
  example: ¬ A :=
    assume h2: A,
    show false, from iff.elim_left h1 h2 h2
end

-- 10.
section
  variable h1: A ↔ ¬ A
  variable h3: ¬ A
  example: A :=
    iff.elim_right h1 h3
end

-- 11.
section
  variable h1: ¬ (A ∨ ¬ A)
  example: ¬ A :=
    assume h2: A,
    show false, from
    h1 (or.inl h2)
end

-- 12.
-- The way Cheng started the problem, it is not possible
-- without classical logic (proof by contradiction).