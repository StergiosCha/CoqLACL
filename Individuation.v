Require Import Bvector.
Require Import Coq.Lists.List.
Require Import Omega.
Load LibTactics.
Unset Implicit Arguments.
Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Ltac AUTO:= cbv delta;intuition;try repeat congruence;  jauto;intuition.
Definition DomCN:=Set.
Record Equiv (A:DomCN) : Type := mkEquiv { eq1:> A->A->Prop; _eq2: reflexive A(eq1)/\ symmetric A eq1/\ transitive A eq1}.
Record CN := mkCN{ B:> DomCN; B2:Equiv B}.
Parameter Human Man : DomCN.
Axiom mh: Man->Human. Coercion mh: Man>->Human.
Parameter IC_Human : Equiv(Human).
Definition HUMAN:= mkCN Human IC_Human.
Parameter John: Human.
Require Import Setoid.
Definition AIC_Man := fun x: Man=>fun y:Man=> IC_Human(x)(y).
Theorem EQ: reflexive  Man  AIC_Man/\  symmetric Man AIC_Man/\  transitive Man AIC_Man. cbv. destruct  IC_Human.
                                                                                        destruct _eq3. destruct H0. split.                                         intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.
Check eq1.
Check _eq2.
Check Equiv.
Check IC_Human.
Definition Three:=fun A:CN=> fun P:A.(B)->Prop=>exists x:A.(B),
P(x)/\exists y:A.(B), P(y)/\ exists z:A.(B), P(z)/\not((A.(B2))(x)(y))/\not((A.(B2))(y)(z)) /\not((A.(B2))(x)(z)).
Parameter walk: HUMAN.(B)->Prop.
Check walk John.
Check (Three HUMAN) walk.
Definition IC_Man:=  mkEquiv Man AIC_Man EQ.
Print IC_Man.
Definition MAN:= mkCN Man IC_Man.
Theorem MANWALK: (Three MAN) walk-> (Three HUMAN) walk. cbv. intros. destruct H.
                                                       destruct H.
                                                       destruct H0. destruct H0.                                                        destruct H1. destruct H1. destruct H2. destruct H3.
                                                       exists x.
                                                       split.                                                        intuition. exists x0. split. intuition. exists x1. split. intuition. intuition. Qed.
Parameter Phy Info: DomCN.
Record PhyInfo : DomCN := mkPhyInfo { phy :> Phy; info :> Info }.
Parameter Book: DomCN.
Axiom bf: Book-> PhyInfo. Coercion bf: Book >-> PhyInfo.
Parameter IC_Phy: Equiv(Phy).
Parameter IC_Info: Equiv(Info).
Definition PHY:= mkCN Phy IC_Phy.
Definition INFO:= mkCN Info IC_Info.
Definition AIC_Book1 := fun x: Book=>fun y:Book=> IC_Phy(x)(y).
Definition AIC_Book2 := fun x: Book=>fun y:Book=> IC_Info(x)(y).
Theorem EQ1: reflexive  Book  AIC_Book1/\  symmetric Book AIC_Book1/\  transitive Book AIC_Book1. cbv. destruct  IC_Phy.
                                                                                        destruct _eq3. destruct H0. split.                                         intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.
 Theorem EQ2: reflexive  Book  AIC_Book2/\  symmetric Book AIC_Book2/\  transitive Book AIC_Book2. cbv. destruct  IC_Info.
                                                                                                   destruct _eq3. destruct H0. split.                                         intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.                                                      Definition IC_Book1:=  mkEquiv Book  AIC_Book1 EQ1.
 Definition IC_Book2:=  mkEquiv Book  AIC_Book2 EQ2.
 Definition Book1:= mkCN Book IC_Book1.
 Definition Book2:= mkCN Book IC_Book2.
 Parameter picked_up: Human->Phy->Prop.
 Parameter mastered: Human->Info->Prop.
 Parameter the: forall A:DomCN, A.
 Check  mastered John (the(Book1.(B))).
 Theorem MASTEREDINFO:(Three Book2) (mastered John)-> (Three INFO)(mastered John).  
   cbv. intros. destruct H. destruct H. destruct H0. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x.
   split.    intuition. exists x0. split. intuition. exists x1. split. intuition. split. intuition. split. intuition. intuition. Qed.
 Theorem pickedupPHY:(Three Book1) (picked_up John)-> (Three PHY)(picked_up John).     cbv. intros. destruct H. destruct H. destruct H0. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x.
                                                                                       split.    intuition. exists x0. split. intuition. exists x1. split. intuition. split. intuition. split. intuition. intuition. Qed.
 Definition AND:= fun A:DomCN=>  fun P: A->Prop=>fun Q:A->Prop=> fun x:A=> P(x) /\ Q(x).
 Theorem pickedupMasteredPHY:(Three Book2) (AND(Book)(picked_up John)(mastered John))-> (Three INFO)(mastered  John).
   cbv. intros. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2. destruct H2. destruct H4. exists x. split. intuition. intuition.  exists x0. intuition. intuition. exists x1. split. intuition. intuition. Qed.   
  Section BOOK.

Variable BOOK1BOOK2: forall x:Book, forall y:Book, IC_Book1  x y-> IC_Book2 x y. 
 Theorem pick1edupMasteredPHY:(Three Book2) (AND(Book)(picked_up John)(mastered John))-> (Three PHY)(picked_up  John).
   cbv. intros. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2. destruct H2. destruct H4. exists x. split. intuition. intuition.  exists x0. intuition. intuition. exists x1. split. intuition.      split. destruct IC_Book2 in BOOK1BOOK2. destruct IC_Book1 in BOOK1BOOK2. destruct _eq3. destruct a. destruct _eq4. destruct a.      destruct IC_Info in H4. destruct IC_Phy. destruct IC_Info in H7. destruct IC_Info in H8. destruct _eq5. destruct _eq4. destruct _eq6. destruct H9. destruct _eq3. destruct H13. destruct H11. unfold transitive in H18. unfold symmetric in H11. unfold reflexive in H10. unfold transitive in H17. unfold symmetric in H13. unfold reflexive in H12. unfold transitive in H14. unfold symmetric in H9. unfold reflexive in H6. destruct H16. unfold transitive in H19. unfold symmetric in H16. unfold reflexive in H15.  AUTO. 