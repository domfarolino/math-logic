-- Simple proof of A /\ A, with a variable and hypothesis that A holds.

variables A B C: Prop
variable h1: B
variable h2: B -> C

-- At this point, we're "applying" h2 to h1. Note that lean is
-- left-associative. Also, to me it is more intuitive to "apply" h1 to h2 here,
-- however lean does not seem to like that.
#check h2 h1