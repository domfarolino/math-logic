-- Assignment 6
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

-- Exercise 1
namespace ex1
  def double: ℕ → ℕ := fun (x: ℕ), x + x
  def do_twice: (ℕ → ℕ) → ℕ → ℕ := fun (f: ℕ → ℕ) (x: ℕ), f (f x)
  def do_thrice (f: ℕ → ℕ) (x: ℕ): ℕ := f (f (f x)) -- From the book.

  -- Some checks.
  #check do_twice double
  #reduce do_twice double 2

  #check do_thrice double
  #reduce do_thrice double 2

  -- My implementation of what the book had:
  def Do_Twice: ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) :=
    fun (outer: (ℕ → ℕ) → ℕ → ℕ) (inner: (ℕ → ℕ)), outer (outer inner)

  #reduce Do_Twice do_twice double 2

  -- Contents from Dr. Cheng's file:
  universe u
  def Do_Twice2 {α: Type u} (g: α → α) (f: α) := g (g f) -- Very general; nice!

  -- Some checks/tests:
  #check Do_Twice2
  #check Do_Twice2 do_twice
  #check Do_Twice2 do_thrice

  #reduce Do_Twice2 do_twice double 2
  #reduce Do_Twice2 do_thrice double 2

  #check Do_Twice2 Do_Twice2
  #reduce Do_Twice2 Do_Twice2 double 2
end ex1

-- Exercise 2
section
  variables α β γ: Type
  variable ab: α × β
  variable test1: α × β → γ
  variable test2: α → β → γ

  def curry (α β γ: Type) (f: α × β → γ): α → β → γ := fun (a: α) (b: β), f (a, b)

  -- A test case:
  def cart_map: (ℕ × ℕ) → ℕ := fun (f: ℕ × ℕ), f.1 + f.2
  #check curry α β γ test1
  #reduce cart_map (10, 2)
  #reduce curry ℕ ℕ ℕ cart_map 10 2

  def uncurry (α β γ: Type) (f: α → β → γ): α × β → γ := fun (a: α × β), f a.1 a.2

  -- A test case:
  def curried_map: ℕ → ℕ → ℕ := fun (a: ℕ) (b: ℕ), a + b
  #check uncurry α β γ test2
  #reduce curried_map 10 2
  #reduce uncurry ℕ ℕ ℕ curried_map (10, 2)
end

-- Exercise 3
namespace ex3
  universe u
  constant vec: Type u → ℕ → Type u

  constant empty: Π α: Type u, vec α 0
  constant cons: Π (α: Type u) (n: ℕ), α → vec α n → vec α (n + 1)
  constant append: Π (α: Type u) (n m: ℕ), vec α m → vec α n → vec α (n + m)

  -- The actual meat of the assignment:
  constant vec_add: Π (α: Type u) (n: ℕ), vec α n → vec α n → vec α n
  constant vec_reverse: Π (α: Type u) (n: ℕ), vec α n → vec α n

  -- Tests:
  variable α: Type u
  variable a: α
  variable n: ℕ
  variables v1 v2: vec α n

  #check empty α
  #check cons α 0 a (empty α)
  #check append α n n v1 v2
  #check vec_add α n v1 v2
  #check vec_reverse α n (vec_add α n v1 v2)
end ex3