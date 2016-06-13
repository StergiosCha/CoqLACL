(** Some Neo-davidsonian Semantics*)
Require Import Bvector.
Require Import Coq.Lists.List.
Require Import Omega.
Load Libtactics.
Ltac AUTO:= cbv delta;intuition;try repeat congruence;  jauto;intuition.
Parameter Agent
Theme: Ind->Event->Prop.  Parameter IN: LOcation->Event->Prop.
Parameter WITH: Instrument->Event->Prop.  Definition In:= fun
x:LOcation=>fun E: Event->Prop=> fun e1:Event=> exists e:Event, E e1/\
IN x e1.  Definition With:= fun x:Instrument=>fun E: Event->Prop=> fun
e1:Event=> exists e:Event, E e1/\ WITH x e1.  Definition stabs:= fun
x:Ind=> fun y:Ind=>fun e1:Event=> exists e:Event, stab x y e /\
Theme(x)(e)/\AGent(y)(e)/\ e=e1.  Parameter a_knife: Instrument.
Parameter Rome Verona Athens: LOcation.  Theorem BRUTUS: (stabs Caesar
Brutus e1)-> AGent(Brutus)(e1). cbv. intro.  destruct H. destruct
H. destruct H0. destruct H1. firstorder. congruence. Qed.  Theorem
BRUTUS1:(In Rome) ((With a_knife) (stabs Caesar Brutus)) e1-> WITH
a_knife e1. AUTO. Qed.  Theorem BRUTUS2:(In Rome) ((With a_knife)
(stabs Caesar Brutus)) e1-> ((With a_knife) (stabs Caesar Brutus))
e1. AUTO. Qed.  Theorem BRUTUS3:(In Rome) ((With a_knife) (stabs
Caesar Brutus)) e1-> ((In Rome) (stabs Caesar Brutus)) e1. AUTO. Qed.
Theorem BRUTUS4:(In Rome) ((With a_knife) (stabs Caesar Brutus)) e1->
((stabs Caesar Brutus)) e1. AUTO. Qed.



