Load test.
Print some.
Let a:=some. 
Theorem EX:(walk) John-> some Man (walk). 
intro. unfold some. exists John. assumption. Qed.


Theorem EX1: some Man (walk) -> (walk) John.
cbv. intro. elim H. intro. intro. replace John with x. 
assumption.

  Theorem EX2:  all Man (walk)->walk John.
    cbv. intro. apply H. Qed.
  
 Theorem EX3: all Man (walk)->walk John->some Man (walk).
  cbv. intros.  exists John. assumption. Qed.


 
 Ltac EXTAC:= cbv; eauto.
 Ltac EXTAC1 x:= cbv; try exists x;EXTAC.

                                 
Theorem EX5  :         all Man (walk)-> some Man (walk). EXTAC1 John. Qed.


                                 
Theorem IRISH: (some Irishdelegate)(On_time Human(finish(the survey)))->(some delegate)(On_time Human(finish(the survey))). 
cbv. intro. elim H. intro. intro. exists x. auto. 
Qed.


Theorem SWE:(a Swede)(Won2(a Nobel_Prize))->(a  Scandinavian)(Won2(a Nobel_Prize)).
  cbv. intros. elim H. intros. exists x. assumption. Qed.

Theorem SWE2:not((a Scandinavian)(Won1(the Nobel_Prize)))->not ((a Swede)(Won1(the  Nobel_Prize))).
  cbv. intro. intro. elim H. elim H0. intros. exists x. assumption. Qed.

Theorem SCAN: (no delegate)(On_time Human(finish(the report)))->not((some Scandinaviandelegate)(On_time Human(finish(the report)))).
  cbv. intro. intro. elim H0. intro. apply H. Qed.

 Theorem ex_imp_ex: forall (A:Type) (P Q:A->Prop), (ex P)-> ( forall x:A, P x -> Q x)->(ex Q).
   intros. elim H. intro. exists x. apply H0. assumption. Qed.
 
Theorem IRISH2: (some delegate)(on_time (finish(the survey)))->(some delegate)((finish
                                                                                  (the survey))).
  cbv. intro.  destruct ADV in H. elim H. intro. intro. exists x0. apply f0. assumption. Qed.  (** on time delegate finish the survey, the second component of VER delegate  finish the survey is a proof that forall x: delegate, on time delegate finish the survey  x -> finish the survey x *)
Theorem FORT: fortunately (walk John)-> walk John.
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
  cbv.  intuition.  Qed.

Theorem GENUINE: (a genuine_diamond)(has John)->(a diamond)(has John).
  cbv.   intro. elim H. intros. exists x. assumption. Qed.

Theorem MICKEY: (Small Animal Mickey) ->not( Large Animal Mickey).
  (** The proof here works due to the lexical semantics of Small, defined as both not large and not normalsized *) cbv. unfold not. intro. apply H. Qed.



Theorem MICKEY2: (all Mouse (Small Animal)/\ Large Mouse Mickey)->not( Large Animal Mickey).
  cbv. intro. elim H. intro. intro. destruct H0 with Mickey. assumption.  Qed.

Set Implicit Arguments. 
Parameter Fast : forall A : CN, A -> Prop.
Parameter FASTER_THAN : forall A : CN, {p : A -> A -> Prop & forall h1 h2 h3 : A, (p h1 h2 /\ p h2 h3 -> p h1 h3) /\ (forall h4 h5 : A, p h4 h5 -> Fast  h4 -> Fast  h5)}.
Definition faster_than:= fun A:CN=>projT1 (FASTER_THAN A).
Parameter PC6082 : Object.
Parameter ITELXZ : Object.
Variables  o1 o2 o3 : Object.
Definition as_fast_as:= fun A:CN=> fun a:A=>fun b:A=> Fast   a ->Fast  b.
Theorem FAST2: faster_than ITELXZ PC6082  /\ Fast ITELXZ -> Fast PC6082. cbv. intro. destruct FASTER_THAN in H. case  a0  with o1 o2 o3. intros. elim H. intros. apply H1 with ITELXZ. assumption. assumption.  Qed.

Theorem KNOW:know John((Won1 (the Contract) ITEL))-> (Won1 (the Contract) ITEL) .
  cbv. destruct FACTIVE. intro. apply p with John. assumption. Qed.

Theorem CONJ:(Signed(the Contract)(and3 Smith Jones Anderson)-> (Signed(the Contract)Smith)).
  cbv. destruct AND3. intro. apply a0. assumption. 

  Theorem CURRENTLY: (Has (a_factory)ITEL) t-> currently (((Has (a_factory)ITEL)))t.
    cbv. intros. destruct H.  AUTO. Qed.

 