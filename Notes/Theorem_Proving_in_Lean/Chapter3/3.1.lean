-- 3.1 Propositions as types

-- We can build our own "proof" and assertion language on top of
-- dependent type theory.

namespace hidden

  -- Introduce a new type `Prop` to represent propositions, as well as
  -- constructors that can build new Props from others.
  variables p q r: Prop

  -- Constructors:
  constant and: Prop → Prop → Prop
  constant or: Prop → Prop → Prop
  constant implies: Prop → Prop → Prop

  #check and p q
  #check or (and p q) r
  #check implies (and p q) (and q p)

  -- For every element p ∈ Prop, we can have a new type called `Proof p`
  -- that represents a proof of the element's existence.

  constant Proof: Prop → Prop

  constant and_comm: Π a b: Prop, Proof (implies (and a b) (and b a))

  #check and_comm
  #check and_comm p q

  -- Modus Ponens.
  -- From a proof of p → q, and p, we obtain a proof of q.
  constant modus_ponens: Π p q: Prop,
    Proof (implies p q) → Proof p → Proof q

  -- Other way around would be nice to have as well:
  constant implies_intro: Π p q: Prop,
    (Proof p → Proof q) → Proof (implies p q)

end hidden