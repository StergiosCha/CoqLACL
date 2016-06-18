Load test.
Definition pr := fun (A : CN) (a : A) =>True.
Set Implicit Arguments. 
Parameter NOT: forall A:CN, (A->Prop)->(Object->Prop).
Parameter Linguist Logician:CN.
Axiom lo:Linguist->Human. Coercion lo:Linguist>->Human.
Axiom lo1:Logician->Human. Coercion lo1:Logician>->Human.
Unset Implicit Arguments. 
Definition PR_o:= fun A:CN=>fun x: Object=>not(    NOT (pr Object)x).
Definition PR_m:= fun A:CN=> fun x: Man=>not(    NOT (pr Man)x).
Definition PR_h:= fun A:CN=> fun x: Human=>not(    NOT (pr Human)x).
Definition PR_l:= fun A:CN=> fun x: Linguist=>not(    NOT (pr Linguist)x).
Definition PR_lo:= fun A:CN=>fun x: Logician=>not(    NOT (pr Logician)x).
Parameter Table: CN.
Axiom to: Table->Object. Coercion to: Table>->Object.
Parameter Red: Object->Prop.

Section NEG.
Variable Classical_Negation: forall P:Prop, not(not P)<->P.
Variable NOT_2hm: forall (a : Human),  NOT  (pr Human) a -> NOT  (pr Man) a.
Variable NOT_2ha: forall (a : Animal), NOT (pr Animal) a -> NOT  (pr Human) a.
Variable NOT_2ao: forall (a : Object), NOT  (pr Object) a -> NOT (pr Animal) a.
Variable NOT_1m: forall x:Man, NOT (pr Man) x-> not(pr Man x).
Variable NOT_1h: forall x:Human, NOT (pr Human) x-> not(pr Human x).
Variable NOT_1a: forall x:Animal, NOT (pr Animal) x-> not(pr Animal x).
Variable NOT_1l:forall x: Linguist, NOT(pr Linguist)x-> not (pr Linguist x).
Variable NOT_1lo:forall x: Logician, NOT(pr Logician)x-> not (pr Logician x).
Theorem NOTNOTMAN: not (NOT (pr Man) John). cbv.
unfold pr in NOT_1m.
jauto. Qed.

Theorem NOTLL : not (forall l:Linguist, PR_l Logician l)
                -> exists l:Linguist, NOT (pr Logician) l. cbv.
intros.
unfold pr in NOT_1l. unfold pr in NOT_1lo.  AUTO.
elim H. 
jauto.
Qed.
Theorem NOTHL: not (forall l:Linguist, PR_l Logician l)
               -> not (forall h:Human, PR_h Logician h). cbv. intros. unfold pr in NOT_1h. unfold pr in NOT_1l.
unfold pr in NOT_1lo. elim H. jauto.
Qed.
  
Theorem NOTHUMANMAN: NOT (pr Human) John -> NOT (pr Man) John.
AUTO. Qed.
End NEG.
Record Redtable :CN := mkRedtable { T :> Table; _ : Red T}.

Theorem TABLE : (all Table) (NOT talk) -> (all Redtable) (NOT talk). cbv. intro.  intros. apply H. Qed. 