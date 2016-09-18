Load test.
Print some.
Let a:=some. 
Theorem EX:(walk) John-> some Man (walk). (**GAUTO  x x x* (here only AUTO is used which takes no arguments, "x x x" are used because GAUTO takes obligatory 3 arguments, they play no role for proofs involving only use of AUTO*)  intro. unfold some. exists John. assumption. Qed.


Theorem EX1: some Man (walk) -> (walk) John. 
cbv. intro. elim H. intro. intro. replace John with x. 
assumption. (**this cannot be proven*)

  Theorem EX2:  all Man (walk)->walk John. (**GAUTO x x x*) 
    cbv. intro. apply H. Qed.
  
 Theorem EX3: all Man (walk)->walk John->some Man (walk). (**GAUTO x x x*)
  cbv. intros.  exists John. assumption. Qed.


 
 Ltac EXTAC:= cbv; eauto.
 Ltac EXTAC1 x:= cbv; try exists x;EXTAC.

                                 
Theorem EX5  :         all Man (walk)-> some Man (walk).  (** AUTOa John x x (here John is needed to be used with exists*)EXTAC1 John. Qed.


                                 
Theorem IRISH: (some Irishdelegate)(On_time Human(finish(the survey)))->(some delegate)(On_time Human(finish(the survey))). (**AUTOa x x x.*)
cbv. intro. elim H. intro. intro. exists x. auto. 
Qed.


Theorem SWE:(a Swede)(Won2(a Nobel_Prize))->(a  Scandinavian)(Won2(a Nobel_Prize)). (**AUTOa x x x.*) 
  cbv. intros. elim H. intros. exists x. assumption. Qed.

Theorem SWE2:not((a Scandinavian)(Won1(the Nobel_Prize)))->not ((a Swede)(Won1(the  Nobel_Prize))). (**AUTOa x x x.*)
  cbv. intro. intro. elim H. elim H0. intros. exists x. assumption. Qed.

Theorem SCAN: (no delegate)(On_time Human(finish(the report)))->not((some Scandinaviandelegate)(On_time Human(finish(the report)))).
(**AUTOa x x x.*)  cbv. intro. intro. elim H0. intro. apply H. Qed.

 
 
Theorem IRISH2: (some delegate)(on_time (finish(the survey)))->(some delegate)((finish
                                                                                  (the survey))). 
  (**AUTOa ADV  x x(ADV  is used so destruct ADV can take effect*) cbv. intro.  destruct ADV in H. elim H. intro. intro. exists x0. apply f0. assumption. Qed.  (** on time delegate finish the survey, the second component of VER delegate  finish the survey is a proof that forall x: delegate, on time delegate finish the survey  x -> finish the survey x *)

Theorem FORT: fortunately (walk John)-> walk John. (**AUTOa ADVS x x (similarly)*) 
cbv. destruct ADVS. apply w. Qed.

Parameter in_Europe: forall A:CN, (A->Prop)->(A->Prop).
Parameter can: forall A:CN, (A->Prop)->(A->Prop). 
Parameter travel: Object->Prop. 
Parameter freely: forall A:CN, (A->Prop)->(A->Prop).
Parameter within_Europe: forall A:CN, (A->Prop)->(A->Prop).
Let each:= all.
Let person:= Human.
Parameter European: CN.
Axiom eu: European->Human. Coercion eu: European>->Human.
Parameter right_to_live_in_Europe:CN.
Parameter have: Object->Human->Prop.


Axiom ro2: right_to_live_in_Europe->Object. Coercion ro2: right_to_live_in_Europe>->Object.

Theorem EUROPEAN: ((each European)(have
(the right_to_live_in_Europe))/\forall x:person, ((have
(the right_to_live_in_Europe)x)->can Human(within_Europe Human (freely Human
(travel)))x))->(each European)(can Human(within_Europe Human(freely Human
                                                                    (travel)))).
(**AUTOa x x x*)   cbv.  intuition.  Qed.

Theorem GENUINE: (a genuine_diamond)(has John)->(a diamond)(has John).
(**AUTOa x x x*)   cbv.   intro. elim H. intros. exists x. assumption. Qed.

Theorem MICKEY: (Small Animal Mickey) ->not( Large Animal Mickey).
  (** The proof here works due to the lexical semantics of Small, defined as both not large and not normalsized *)(**AUTOa x x x.*)  cbv. unfold not. intro. apply H. Qed.



Theorem MICKEY2: (all Mouse (Small Animal)/\ Large Mouse Mickey)->not( Large Animal Mickey). (**AUTOa H1 x H1.*)  cbv. intro. elim H. intro. intro. destruct H0 with Mickey. assumption.  Qed.

Set Implicit Arguments. 
Parameter Fast : forall A : CN, A -> Prop.
Parameter FASTER_THAN : forall A : CN, {p : A -> A -> Prop & forall h1 h2 h3 : A, (p h1 h2 /\ p h2 h3 -> p h1 h3) /\ (forall h4 h5 : A, p h4 h5 -> Fast  h4 -> Fast  h5)}.
Definition faster_than:= fun A:CN=>projT1 (FASTER_THAN A).
Parameter PC6082 : Object.
Parameter ITELXZ : Object.
Variables  o1 o2 o3 : Object.
Definition as_fast_as:= fun A:CN=> fun a:A=>fun b:A=> Fast   a ->Fast  b.
Theorem FAST2: faster_than ITELXZ PC6082  /\ Fast ITELXZ -> Fast PC6082. cbv. intro. destruct FASTER_THAN in H.   case  a0 with o1 o2 o3. intros. elim H. intros. apply H1 with ITELXZ. assumption. assumption. Qed. (**This can be semiautomated with the existing tactics:  cbv. intro. destruct FASTER_THAN in H.   case  a0 with o1 o2 o3. AUTOa x x x.*)

Theorem KNOW:know John((Won1 (the Contract) ITEL))-> (Won1 (the Contract) ITEL) .  
(**AUTOa FACTIVE A B(this makes use of all the arguments, given that the first argument is always destructed as A B, we use A and B for the next two arguments of AUTOa*)cbv. destruct FACTIVE. intro. apply p with John. assumption. Qed.

Theorem CONJ:(Signed(the Contract)(and3 Smith Jones Anderson)-> (Signed(the Contract)Smith)). 
(**AUTOa AND3 A B.*)   cbv. destruct AND3. intro. apply a0. assumption. 

  Theorem CURRENTLY: (Has (a_factory)ITEL) t-> currently (((Has (a_factory)ITEL)))t.
 (**AUTOa x x x.*)    cbv. intros. destruct H.  AUTO. Qed.
