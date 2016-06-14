Require Import Bvector.
Require Import Coq.Lists.List.
Require Import Omega.
Load LibTactics.
Unset Implicit Arguments.
Inductive vector (A : Type) : nat -> Type :=
    Vnil : vector A 0
  | Vcons : A -> forall n : nat, vector A n -> vector A (S n).
Notation "a :: b" := (Vcons  a b).
Definition CN:= Set.
                (** Common Nouns as Types *)
                 Parameter Bank Manager Accountant Car Meeting HumanTypes City Nobel_Prize Distance Mammal Report Student Diamond Delegate Location Time Duration Mouse Survey Swede Scandinavian Contract Door Window Institution Phy Info Factory Woman Man Object President Surgeon Animal Human:CN.
      (* *Book as a Sigma Type encoding Pustejovsky's qualias structure. The first projection is coerction, thus Book is a subtype of phy.info The and dot*)
Record PhyInfo : CN := mkPhyInfo { phy :> Phy; info :> Info }.
(* Book as Sigma-type with PhyInfo & BookQualia *)
Parameter Hold : Phy->Info->Prop.
Parameter R1 : PhyInfo->Prop.
Parameter W : Human->PhyInfo->Prop.
Record BookQualia (A:PhyInfo) : Set :=
mkBookQualia { Formal : Hold A A;
Telic : R1 A;
Agent : exists h:Human, W h A }.
Record Book : Set := mkBook { Arg :> PhyInfo; Qualia : BookQualia Arg }.

     (** Subtyping relations. Coercion ensures that in every situation *)
Axiom do: Diamond->Object. Coercion do: Diamond >-> Object.
Axiom ph1: President->HumanTypes. Coercion ph1: President>->HumanTypes.
Axiom hh1: HumanTypes->Human. Coercion hh1: HumanTypes>->Human.
Axiom sw: Surgeon -> Human. Coercion sw: Surgeon >-> Human.
Axiom mo2: Meeting->Object. Coercion mo2: Meeting>->Object.
Axiom mh2: Manager->Human. Coercion mh2: Manager >-> Human.
Axiom co3: Car->Object. Coercion co3: Car>-> Object.
Axiom co2: City->Object. Coercion co2: City>-> Object.
Axiom maa: Mammal->Animal. Coercion maa: Mammal >-> Animal.
Axiom no1: Nobel_Prize ->Object. Coercion no1: Nobel_Prize>->Object.
Axiom sh1: student->Human. Coercion sh1: student>->Human.
Axiom dh:delegate->Human. Coercion dh: delegate>->Human.
Axiom dt: Duration->Time. Coercion dt:Duration>->Time.
Axiom fo:factory->Object. Coercion fo: factory>->Object.
Axiom ma: Mouse ->Animal. Coercion ma:Mouse>->Animal.
Axiom mh : Man->Human. Coercion mh : Man >-> Human.
Axiom wh : Woman->Human. Coercion wh : Woman >-> Human.
Axiom ha: Human-> Animal. Coercion ha: Human>-> Animal.
Axiom ao: Animal->Object. Coercion ao: Animal>-> Object.
Axiom DH: Door->Object. Coercion DH: Door>->Object.
 Axiom WH: Window->Object. Coercion WH: Window>->Object.
Axiom COB: Contract->Object. Coercion COB: Contract>->Object.
Axiom sh: Scandinavian->Human. Coercion sh: Scandinavian>->Human.
Axiom ss: Swede->Scandinavian. Coercion ss: Swede>-> Scandinavian.
Axiom so: survey->Object. Coercion so:survey>->Object.
Axiom cl: City->Location. Coercion cl: City>->Location.
Axiom ro1: report->Object. Coercion ro1: report>->Object.
(** Some quantifiers *)
Definition some:= fun A:CN=> fun P:A->Prop=> exists x:A, P(x). 
Definition all:= fun A:CN=> fun P:A->Prop=> forall x:A, P(x).
Definition no:= fun A:CN=> fun P:A->Prop=> forall x:A, not(P(x)).
Let a:= some.
Let each:=all.

(** Factive verbs as first projections of a general FACTIVE Sigma *)
Parameter FACTIVE: sigT (fun p: Human->Prop->Prop => forall h:Human, forall P:Prop, p h P -> P).
Definition know:= projT1 FACTIVE.
Definition saw:= projT1 FACTIVE.
(** Same for conjunction and disjunction. No general conjunction rule given here, this is for 2 place and three place conjunction *)
Set Implicit Arguments. 

Parameter AND: forall A:Type, forall x y :A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)).
Definition and:= fun A:Type=> fun x y:A=>projT1(AND x y).
Parameter AND3: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)/\ p(z)).  
Definition and3:= fun A:Type=> fun x y z:A=>projT1(AND3 x y z).
Parameter DIS: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) -> p(x) \/p(y )\/ p(z)).  
Definition or3:= fun A:Type=> fun x y z:A=>projT1(DIS x y z).
(** Regular VP conjunction if you do not like the above *)
Definition AND1:= fun A:CN=>  fun P: A->Prop=> fun Q:A->Prop=>fun x:A=>P(x) /\Q(x).
(** Adjectives, intersective as regular predicates, subsectives as polymorphic predicates, privative as disjoint union types and former as involving time parameters *)
Unset Implicit Arguments. 
Parameter boring : Info->Prop.
Parameter Large Normalsized: forall A:CN, A->Prop.
Definition Small:= fun A:CN=>fun a:A=> not (Large A(a))/\ not (Normalsized A(a)).
Parameter genuine: Object->Prop.
Parameter short:Human->Prop.
Parameter Irish: Object->Prop.
Parameter scandinavian:Object->Prop.

(** Comparatives again involving an auxiliary Sigma. Two versions, one with height parameters one without. The one with height parameters presuspposes that Common Nouns can be indexed with height parameters. Here we shown the indexed type for Human, i.e. Humans indexed with heights *)
Definition height:= nat.
Inductive HUMAN : nat -> Type :=  HUMAN1 : forall n : nat, HUMAN n.
Parameter J G: sigT(fun x:height=> HUMAN x).
Definition j:= projT2 J.
Definition g:= projT2 G.
Parameter SHORTER_THAN: sigT(fun p:Human->Human->Prop=> forall h1:Human,forall h2:Human,forall h3:Human, (p(h1)(h2)/\ p(h2)(h3)->p(h1)(h3))/\     forall
h1 h2:Human, p h1 h2 -> (short(h2)-> short (h1))).
Definition shorter_than:=  projT1(SHORTER_THAN).
Parameter SHORTER_THAN1:forall i j : height, sigT( fun p : HUMAN i -> HUMAN j -> Prop =>forall (h1 : HUMAN i) (h2 : HUMAN j), p h1 h2 <-> gt i j).
Definition shorter_than1 :=fun i j : height => projT1 (SHORTER_THAN1 i j).
(** experimenting with defining quantifiers using vectors *)
Definition three :=fun (A : CN)  (P :forall n:nat, vector A n ->Prop)=>exists x:nat, exists z : vector A x, P x z /\ ge x 3.
Definition NO:=fun (A : CN) (P : forall n : nat, vector A n -> Prop) =>forall (n : nat) (z : vector A n), ~ P n z.
Definition exactly_one :=fun (A : CN)  (P :forall n:nat, vector A n ->Prop)=>exists! x:nat, exists z : vector A x, P x z /\ x = 1/\ forall n:nat, forall z: vector A n, not (P n z).
(** Experimenting with a simple model of tense. A time parameter is assumed as an argument for verbs *)
Parameter sign: Object->Human->Time->Prop.
Parameter Interval: list Time->Time.
Parameter fouryears:list Time.
Definition FOR:= fun T: list Time=> fun P:Time ->Prop=> fun t:Time=> P(t) /\ Interval(T) = t /\ forall t1:Time, In t1 T -> P(t1).
Definition Year:= nat.
Definition Month:= nat.
Definition Day:= nat.
Parameter default_y:Year.
Parameter default_m:Month.
Parameter default_d: Day.
Parameter DATE : Year -> Month -> Day -> Time.
Let default_t:= DATE default_y default_m default_d.
Definition currently:=fun P : Time -> Prop=> P default_t.
Parameter Have: Object->Human->Time->Prop.
Definition Has:=fun (x : Object)(y : Human) (t : Time)=>
Have x y t /\ t = default_t.
Parameter On_time: forall A:CN, (A->Prop)->(A->Prop). 
Parameter live: Location->Human->Time->Prop.
Parameter run : forall n : nat, vector Human n -> Prop.
Parameter precedes : Time -> Time -> Prop .
Definition reflexive_precedes:= fun  t:Time =>  precedes t t .
Definition lived:= fun x:Location=> fun y:Human=> fun t:Time=> live x y t/\precedes t default_t.
Definition signed:=fun (x : Object) (y : Human) (t : Time) =>
sign x y t /\ precedes t (DATE default_y default_m
default_d).
