-- 2.4 Introducing Definitions

-- To define a new "object", we use the `def` keyword. This allows
-- us to create something, with a type, that we can reference later
-- via some name, and prove things about.

def foo: ℕ → ℕ := fun (x: ℕ), x + 2

-- Basic check.
#check foo -- Going to be the type that we defined just before "foo".

-- Basic reductions.
constant x: ℕ
#reduce foo x -- Going to carry out all of the abstract computations
              -- necessary/warranted by the expressed logic.

#reduce foo 2

-- Alternate syntax of the above function:
def foo' (x: ℕ): ℕ := x + 2
--           ^___^
--          ℕ  →  ℕ (this is really manifested in the above form).

-- More examples (some of which employ the new cool-kid syntax we learned).
def double (x: ℕ): ℕ := x + x
#reduce double 10 -- 20 :)

def square (x: ℕ): ℕ := x * x
#reduce square 10 -- 100 :)

def do_twice (f: ℕ → ℕ) (x: ℕ): ℕ := f (f x)
def do_twice_longhand: (ℕ → ℕ) → ℕ → ℕ := fun (f: ℕ → ℕ) (x: ℕ), f x

-- Another example of the short- and long-hand definitions:
section
  def f (x : ℕ) : ℕ := x + 7
  def f': ℕ → ℕ := fun (a: ℕ), a + 7
  def f'' (x: ℕ) (y: ℕ ): ℕ := x + y

  #check f
  #check f'
  #check f''

  #reduce f 4
  #reduce f' 4
end

-- Examples
#reduce do_twice double
#reduce do_twice double 2

#reduce do_twice square
#reduce do_twice square 2

def square_twice (x: ℕ): ℕ := do_twice square x
#reduce square_twice 4

constant a: ℕ
def do_once (outer: (ℕ → ℕ) → ℕ → ℕ) (inner: ℕ → ℕ) := outer inner

-- Checks and reduces.
#check do_once
#check do_once do_twice
#check do_twice -- Same as above.

#reduce ((do_once do_twice) double) a
#reduce do_once do_twice double 2

-- Exercise: "We encourage you to try defining a function":
-- Do_Twice: ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ)

def Do_Twice: ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) :=
  fun (outer: (ℕ → ℕ) → ℕ → ℕ) (inner: (ℕ → ℕ)), outer (outer inner)

#reduce Do_Twice do_twice double 2

-- See assignment for the curry/uncurry exercise of this section.