Require Import Reals.
Load Clean_inference.
(** Dealing with multidimensional adjectives. Health as an inductive type where the dimensions are enumerated. This is just an enumerated type*)
Inductive Health: CN:= Heart|Blood|Cholesterol.
Parameter Degree:R.
Parameter healthy: Health->Human->Prop.
Definition Sick:=fun y : Human => ~ (forall x : Health, healthy x y).
Definition Healthy:= fun y : Human => forall x : Health, healthy x y.

(**This is sort of a hack. Given that in Coq, coercions do not propagate thrugh the constructors as in TTCS, we show the case of two Irish delegate entries, one where Human is the first projection and the other where IrishHuman is. Then, we define a unit type Irishdelegate that includes both types.*)
Record Irishhuman : CN := mkIrishhuman { l3 :> Human; _ : Irish l3 }.
Record Irishdelegate : CN := mkIrishdelegate { c :> delegate; _ : Irish c }.
Record Irishdelegate1 : CN := mkIrishdelegate1 { c3 :> Irishhuman; _ : Irish c3 }.
Inductive OneIrishdelegate : Set :=  IrishDelegate.
Definition Ir1 (r:OneIrishdelegate):CN:=Irishdelegate. Coercion Ir1: OneIrishdelegate>->CN.
Definition Ir2 (r:OneIrishdelegate) :Set:=Irishdelegate1. Coercion Ir2: OneIrishdelegate>->Sortclass.
Parameter Black:Object->Prop.
(** Same idea for black man*)
Record Blackman : CN := mkBlackman { l4 :> Man; _ : Black l4 }.
Record Blackhuman : CN := mkBlackhuman { l5 :> Human; _ : Black l5 }.
Record Blackman1 : CN := mkBlackman1 { c4 :> Blackhuman; _ : Black c4 }.
Inductive OneBlackman : Set :=  BlackMan.
Definition Br1 (r:OneBlackman):CN:=Blackman. Coercion Br1: OneBlackman>->CN.
Definition Br2 (r:OneBlackman) :Set:=Blackman1. Coercion Br2: OneBlackman>->Sortclass.
