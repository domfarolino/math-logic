-- Assignment 6
-- Dom Farolino, farolidm@mail.uc.edu
-- Math Logic

-- Exercise 1
section
  def double: ℕ → ℕ := fun (x: ℕ), x + x
  def do_twice: (ℕ → ℕ) → ℕ → ℕ := fun (f: ℕ → ℕ) (x: ℕ), f (f x)

  def Do_Twice: ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) :=
    fun (outer: (ℕ → ℕ) → ℕ → ℕ) (inner: (ℕ → ℕ)), outer (outer inner)

  #reduce Do_Twice do_twice double 2
end

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

  def uncurry (α β γ: Type) (f: α → β → γ): α × β → γ := fun a, f a.1 a.2

  -- A test case:
  def curried_map: ℕ → ℕ → ℕ := fun (a: ℕ) (b: ℕ), a + b
  #check uncurry α β γ test2
  #reduce curried_map 10 2
  #reduce uncurry ℕ ℕ ℕ curried_map (10, 2)
end

-- Exercise 3
namespace ex3
  universe u

  constant nil: Π {α: Type u}, list α
  constant cons: Π {α: Type u}, α → list α → list α

  -- The actual meat of the assignment:
  constant add_two_vecs : Π {α : Type u}, list α → list α → list α
  constant reverse_vec: Π {α: Type u}, list α → list α

  variable α: Type
  variable x: α

  #check add_two_vecs (cons x nil) (cons x nil)
  #check reverse_vec (cons x (cons x nil))
end ex3