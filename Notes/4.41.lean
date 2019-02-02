-- 4.40 Forward Reasoning, another example (hence 4.41)

-- Traditionally, we can write the following proof as:
variables A B C: Prop

example: (A → (B → C)) → (A ∧ B → C) :=
assume h1 : A → (B → C),
assume h2 : A ∧ B,
show C, from h1 (and.left h2) (and.right h2)

-- We can write it with more of a forward-reasoning style as:
example: (A → (B → C)) → (A ∧ B → C) :=
assume h1 : A → (B → C),
assume h2 : A ∧ B,
have h3: B -> C, from h1 (and.left h2),
show C, from h3 (and.right h2)

-- Furthermore, consider:
example: (A → (B → C)) → (A ∧ B → C) :=
assume h1 : A → (B → C),
assume h2 : A ∧ B,
have h3: B, from (and.right h2),
have h4: B -> C, from h1 (and.left h2),
show C, from h4 h3