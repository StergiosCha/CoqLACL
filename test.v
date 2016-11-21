Require Import Bvector.
Require Import Coq.Lists.List.
Require Import Omega.
Load LibTactics.
Unset Implicit Arguments.
Inductive vector (A : Type) : nat -> Type :=
    Vnil : vector A 0
  | Vcons : A -> forall n : nat, vector A n -> vector A (S n).
Notation "a :: b" := (Vcons  a b).
Definition CN := Set.
Definition CNpl:= Set.
Parameters accountants men women:CNpl.
Parameter bank manager accountant car meeting humantypes city nobel_prize distance mammal report student diamond delegate location time duration mouse survey swede scandinavian contract door window institution Phy Info factory woman man object president surgeon animal human:CN.
Parameter a_factory:factory.
Parameters t t1 t2 t3:time.
Parameter birmingham:city.
Parameter chairman_of_itel: man.
Parameter cars: car.
Parameter surgeon1: human->Prop.
Parameter scandinavian1:object->Prop.
Axiom do: diamond->object. Coercion do: diamond >-> object.
Axiom ph1: president->humantypes. Coercion ph1: president>->humantypes.
Axiom hh1: humantypes->human. Coercion hh1: humantypes>->human.
Axiom sw: surgeon -> human. Coercion sw: surgeon >-> human.
Axiom mo2: meeting->object. Coercion mo2: meeting>->object.
Axiom mh2: manager->human. Coercion mh2: manager >-> human.
Axiom co3: car->object. Coercion co3: car>-> object.
Axiom co2: city->object. Coercion co2: city>-> object.
Axiom maa: mammal->animal. Coercion maa: mammal >-> animal.
Axiom no1: nobel_prize ->object. Coercion no1: nobel_prize>->object.
Axiom sh1: student->human. Coercion sh1: student>->human.
Axiom dh:delegate->human. Coercion dh: delegate>->human.
Axiom dt: duration->time. Coercion dt:duration>->time.
Axiom fo:factory->object. Coercion fo: factory>->object.
Axiom ma: mouse ->animal. Coercion ma:mouse>->animal.
Axiom mh : man->human. Coercion mh : man >-> human.
Axiom wh : woman->human. Coercion wh : woman >-> human.
Axiom ha: human-> animal. Coercion ha: human>-> animal.
Axiom ao: animal->object. Coercion ao: animal>-> object.
Axiom DH: door->object. Coercion DH: door>->object.
 Axiom WH: window->object. Coercion WH: window>->object.
Axiom COB: contract->object. Coercion COB: contract>->object.
Axiom sh: scandinavian->human. Coercion sh: scandinavian>->human.
Axiom ss: swede->scandinavian. Coercion ss: swede>-> scandinavian.
Axiom so: survey->object. Coercion so:survey>->object.
Axiom cl: city->location. Coercion cl: city>->location.
Axiom ro1: report->object. Coercion ro1: report>->object.
Parameter opened: human->object->Prop.
Parameter has: human->object->Prop.
Parameter IN1: object->location.
Parameter four_legged: animal->Prop.
Parameter precedes : time -> time -> Prop .
Definition reflexive_precedes:= fun  t:time =>  precedes t t .
Parameter Signed: object->human->Prop.
Parameter won: object->human->time->Prop.
Parameter won1:object->human->Prop. 
Parameter run: human->Prop.
Parameter irish: object->Prop.
Parameter john george anderson smith jones:man.
Parameter mary: woman.
Parameter fido dumbo: animal. 
Parameter itel: human.
Parameter mickey: mouse.
Parameter large normalsized: forall A:CN, A->Prop.
Definition small:= fun A:CN=>fun a:A=> not (large A(a))/\ not (normalsized A(a)).
Parameter genuine: object->Prop.
Parameter the: forall A:CN, A.
Parameter talk cycle drive: human->Prop.
Parameter attack killed: animal -> animal -> Prop.
Definition some:= fun A:CN=> fun P:A->Prop=> exists x:A, P(x).
Definition all:= fun A:CN=> fun P:A->Prop=> forall x:A, P(x).
Definition no:= fun A:CN=> fun P:A->Prop=> forall x:A, not(P(x)).
Parameter read : human->Info->Prop.
Parameter finish: object->human->Prop. 
Parameter And: forall A:Type, A->A->A. 
Record PhyInfo : CN := mkPhyInfo { phy :> Phy; info :> Info }.
(* Book as Sigma-type with PhyInfo & BookQualia *)
Parameter Hold : Phy->Info->Prop.
Parameter R : PhyInfo->Prop.
Parameter W : human->PhyInfo->Prop.
Record BookQualia (A:PhyInfo) : Set :=
mkBookQualia { Formal : Hold A A;
Telic : R A;
Agent : exists h:human, W h A }.
Record Book : Set := mkBook { Arg :> PhyInfo; Qualia : BookQualia Arg }.
Parameter boring : Info->Prop.
Record BBook : CN := mkBBook { b :> Book; _ : boring b }.
Record irishdelegate : CN := mkIrishdelegate { c :> delegate; _ : irish c }.
Record scandinaviandelegate : CN := mkScandinaviandelegate { e :> delegate; _ : scandinavian1 e }.
Record genuine_diamond : CN := mkgenuine_diamond { f :> diamond; _ : genuine f}.
Parameter won2:object->human->Prop.
Parameter won3:((object->Prop)->Prop)->human->Prop.
Parameter hit: human->human->Prop.
Definition not1:= fun A:CN=> fun P:A->Prop=> fun x:A=> not(P x).
Set Implicit Arguments. 
Parameter ADV: forall (A : CN) (v : A -> Prop),sigT  (fun p : A -> Prop =>
 forall x : A, p x -> v x).
Definition on_time:= fun A:CN=> fun v:A->Prop=> projT1 (ADV(v)).
Parameter ADVS: forall ( v : Prop), sigT  (fun p : Prop => p  ->  v).
Definition fortunately:= fun v:Prop=>projT1 (ADVS v).
Unset Implicit Arguments. 
Inductive HUMAN : nat -> Type :=  HUMAN1 : forall n : nat, HUMAN n.
Parameter short:human->Prop.
Definition height:= nat.
Parameter J G: sigT(fun x:height=> HUMAN x).
Definition j:= projT2 J.
Definition g:= projT2 G.
Set Implicit Arguments.
Parameter SHORTER_THAN: sigT(fun p:human->human->Prop=> forall h1:human,forall h2:human,forall h3:human, (p(h1)(h2)/\ p(h2)(h3)->p(h1)(h3))/\     forall
h1 h2:human, p h1 h2 -> (short(h2)-> short (h1))).
Definition shorter_than:=  projT1(SHORTER_THAN).
Parameter SHORTER_THAN1:forall i j : height, sigT( fun p : HUMAN i -> HUMAN j -> Prop =>forall (h1 : HUMAN i) (h2 : HUMAN j), p h1 h2 <-> gt i j).
Definition shorter_than1 :=fun i j : height => projT1 (SHORTER_THAN1 i j).
Unset Implicit Arguments.
Fixpoint nth3 (A : Type) (n g : nat) (l : vector A g) (default : A) {struct l}: A :=match n with | 0 => match l with| Vnil _ => default| Vcons _ x _ _ => x end | S m =>match l with| Vnil _ => default| Vcons _ x n0 t => nth3 A m n0 t x end end.  
Definition each_other1:=fun (n : nat) (P : human -> human -> Prop) (u : vector human (n + 2))=>forall i j : nat,i <= n + 2 /\ j <= n + 2 /\ i <> j ->exists d : human,exists g : human, P (nth3 human i (n + 2) u d) (nth3 human j (n + 2) u g) /\P (nth3 human j (n + 2) u g) (nth3 human i (n + 2) u d). 
Parameter sign: object->human->time->Prop.
Parameter Interval: list time->time.
Parameter fouryears:list time.
Definition FOR:= fun T: list time=> fun P:time ->Prop=> fun t:time=> P(t) /\ Interval(T) = t /\ forall t1:time, In t1 T -> P(t1).
Definition Year:= nat.
Definition Month:= nat.
Definition Day:= nat.
Parameter default_y:Year.
Parameter default_m:Month.
Parameter default_d: Day.
Parameter DATE : Year -> Month -> Day -> time.
Let default_t:= DATE default_y default_m default_d.
Definition currently:=fun P : time -> Prop=>fun t:time=> P default_t.
Parameter have: object->human->time->Prop.
Definition has1:=fun (x : object)(y : human) (t : time)=>
                  have x y t /\ t = default_t.
(**attempt to use tense information, so this says that has is true if a have relation holds in a present moment**)
Parameter on_time1: forall A:CN, (A->Prop)->(A->Prop). 
Parameter live: location->human->time->Prop.
Definition three :=fun (A : CN)  (P :forall n:nat, vector A n ->Prop)=>exists x:nat, exists z : vector A x, P x z /\ ge x 3.
Definition NO:=fun (A : CN) (P : forall n : nat, vector A n -> Prop) =>forall (n : nat) (z : vector A n), ~ P n z.

Parameter run1 : forall n : nat, vector human n -> Prop.
Definition lived:= fun x:location=> fun y:human=> fun t:time=> live x y t/\precedes t default_t.
Definition signed:=fun (x : object) (y : human) (t : time) =>
sign x y t /\ precedes t (DATE default_y default_m
default_d).
Parameter FACTIVE: sigT (fun p: human->Prop->Prop => forall h:human, forall P:Prop, p h P -> P).
Definition know:= projT1 FACTIVE.
Definition saw:= projT1 FACTIVE.
Set Implicit Arguments.
Parameter AND: forall A:Type, forall x y :A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)).  
Definition and:= fun A:Type=> fun x y:A=>projT1(AND x y).
Parameter AND3: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)/\ p(z)).  
Definition and3:= fun A:Type=> fun x y z:A=>projT1(AND3 x y z).
Parameter DIS: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) -> p(x) \/p(y )\/ p(z)).  
Definition or3:= fun A:Type=> fun x y z:A=>projT1(DIS x y z).
Unset Implicit Arguments.
Parameters cycles drives: human->Prop.
Parameter stergios zhaohui: human.
Variable d: swede. 
Variable n: nobel_prize.
Parameter walk:animal->Prop.
Inductive PRESIDENT :time -> Type :=  PRESIDENT1 : forall t : time, PRESIDENT t.
Definition former:=fun x : time -> CN =>(x default_t -> False) /\ (exists t : time, precedes t default_t /\ (PRESIDENT t -> True)).
Definition last_year1 :=fun (P : time -> Prop) =>P (DATE (default_y - 1) default_m default_d).
Parameter meettr: human->human->Prop.
Definition meetc :=fun (n : nat) (u : vector human (n + 2))=>forall i j : nat,i <= n + 2 /\ j <= n + 2 /\ i <> j ->exists d : human,exists g : human, meettr (nth3 human i (n + 2) u d) (nth3 human j (n + 2) u g) /\meettr (nth3 human j (n + 2) u g) (nth3 human i (n + 2) u d).  
Definition each_other :=fun (n : nat) (P : human -> human -> Prop) (u : vector human (n + 2))=>forall i j : nat,i <= n + 2 /\ j <= n + 2 /\ i <> j ->exists d : human,exists g : human, P (nth3 human i (n + 2) u d) (nth3 human j (n + 2) u g) /\P (nth3 human j (n + 2) u g) (nth3 human i (n + 2) u d). 
Definition respectively :=fun (n : nat) (u : vector human (n + 2))( v: vector (human->Prop) (n+2))=>forall i j : nat,i <= n + 2 /\ j <= n + 2 /\ i <> j ->exists d : human,exists g : human, exists P:human->Prop, exists Q:human->Prop,  ((nth3 (human->Prop)) i (n + 2) v P) (nth3 human i (n + 2) u d) /\ ((nth3 (human->Prop)) j (n + 2) v Q) (nth3 human j (n + 2) u g).
Definition last_year:= fun P : time -> Prop => exists m : nat, exists n : nat, P (DATE (default_y - 1) m n) /\ m <= 30 /\ 7 <= n.
Ltac AUTO:= cbv delta;intuition;try repeat congruence;  jauto;intuition.
Definition NOW:= fun m: nat=> fun n:nat=> fun l:nat=> default_t = DATE m n l /\ default_y = m /\ default_m = n /\ default_d = l.

Ltac AUTOa  x i g:= cbv;try exists x;try destruct x as (A,B);try destruct x as (A);try apply i; try apply g;try intro;try ecase i;  AUTO;  try eapply i;try ecase g; AUTO; try eapply g; try omega; AUTO; intuition; try repeat congruence; jauto;intuition.
Ltac GAUTO x i g:= try  solve[AUTO]; try solve [AUTOa x i g].
 
