-- Simple proof of A /\ A, with a variable and hypothesis that A holds.

variable A: Prop
variable h1: A

#check (and.intro h1 h1)