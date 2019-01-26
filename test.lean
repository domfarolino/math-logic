variables A B : Prop
variable h : A /\ not B

#check and.left h
#check and.right h
#check and.intro (and.left h) (and.right h)
