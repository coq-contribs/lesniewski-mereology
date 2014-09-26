Require Import Coq.Init.Tactics.
Require Import Relation_Definitions.
Require Import Coq.Program.Basics.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Structures.Equalities.
Require Import Relation_Definitions Setoid.
Require Import Coq.Classes.Morphisms.


Module Mereology.

(************************** Basic Lemmas ***************************)

Notation "a ≡≡ b" := (iff a b)  (at level 70).

Structure Morphism  : Type := {
  f       :> Prop -> Prop;
  compat  : forall (x1 x2: Prop), (x1 ≡≡ x2) ≡≡ (f x1 ≡≡ f x2)}.
(* these of extensionality *)

Add Parametric Morphism  (M : Morphism) :
            (@f M) with signature (@iff ==> @iff) as extensional_prop.
Proof. 
apply (compat M).
Qed. 

Lemma ProtoT1 : forall (p q:Prop)(F:Morphism), (p ≡≡ q) -> (F p ≡≡ F q).
Proof.
intros a b F H.
rewrite H. 
reflexivity.
Qed. 

Lemma Proto01 : forall P Q:Prop, P -> P \/ Q.
Proof.
intros. left. assumption.
Qed.

Lemma Proto02 : forall P :Prop, P -> P.
Proof.
intros P H. 
auto.
Qed.

(* ====================== ONTOLOGICAL AXIOM  ============================= *)

(* explication p 283 -> no typing on singulars and plurals *)

Class N : Type.
Class epsilon (A a:N) : Prop.

Notation "A 'ε' b" := (epsilon A b)  (at level 70). 

Axiom isEpsilon : forall A a, A ε a ≡≡ ((exists B, B ε A) /\ 
                              (forall C D, (C ε A /\ D ε A) -> C ε D) /\
                              (forall C, C ε A  -> C ε a)).


(* =========================== ONTOLOGICAL DEFINITIONS =============================== *)

Definition exist_at_least      := fun a => exists A, A ε a.  (* D1 *)

Definition exist_at_most       := fun a => forall B C, B ε a /\ C ε a -> B ε C. (* D2 *) 

Definition exist_exactly       := fun A => forall b, A ε b. (* D3 *)

Definition singular_equality   := fun A B => A ε B /\ B ε A. (* D4 *)

Definition singular_difference := fun A B =>  A ε A /\ B ε B /\ ~singular_equality A B. (* D5 *)

Definition weak_equality       := fun a b => forall A, (A ε a) ≡≡ (A ε b). (* D6 *)

Definition strong_equality     := fun a b => (exists G, G ε a) /\ forall G,  (G ε a) ≡≡ (G ε b). (* D7 *)

Definition weak_inclusion      := fun a b => forall A, A ε a -> A ε b. (* D8 *)

Definition strong_inclusion    := fun a b => (exists G, G ε a) /\ forall G, G ε a -> G ε b. (* D9 *)

Definition partial_inclusion   := fun a b => exists G, G ε a /\ G ε b. (* D10 *)

(* logical properties *)
 
Parameter empty                : N.
Parameter universal            : N.
Parameter distinct             : N -> N.

Definition empty_name       := fun A => (A ε A /\ ~(A ε A)). (*D13*)
Parameter empty_equi        : forall A, A ε empty ≡≡ empty_name A.

Definition universal_name   := fun A => A ε A. (*D14*)
Parameter univ_equi         : forall A, A ε universal ≡≡ universal_name A.

Definition distinct_from    := fun A b => (A ε A /\ ~(A ε b)). (*D15*)
Parameter distinct_equi     : forall A b,  A ε (distinct b) ≡≡ distinct_from A b. 

(* =========================== ONTOLOGICAL THEOREMS =============================== *)

Class Antisymmetric  (R:relation N) :=
      antisymmetry : forall a b, R a b /\ R b a -> singular_equality a b.

Class POR_N (R:relation N) := {
   por_refl    :> Reflexive R;
   por_antisym :> Antisymmetric R;
   por_trans   :> Transitive R}.

Lemma LO01 : forall A:N, A ε A -> singular_equality A A.
Proof.
intros A H1.
red; split; [ exact H1 | exact H1 ].
Qed.

Lemma OntoT0 : forall A a, A ε a -> forall C, (C ε A -> C ε A).
Proof.
intros.
assumption.
Qed.

Lemma OntoT1 : forall A a:N, A ε a -> exists B, B ε A.
Proof.
intros A a H0.
apply isEpsilon in H0.
decompose [and] H0.
assumption.
Qed.

Lemma OntoT2 : forall A a:N, A ε a -> (forall C D, (C ε A /\ D ε A) -> C ε D).
Proof.
intros A a H0.
apply isEpsilon in H0. 
decompose [and] H0.
assumption.
Qed.

Lemma OntoT3 : forall A a:N, A ε a -> forall C, C ε A -> C ε a.
Proof.
intros A a H0.
apply isEpsilon in H0. 
decompose [and] H0.
assumption.
Qed.

Lemma OntoT4 : forall A a, ((exists B, B ε A) /\ 
                            (forall C D, (C ε A /\ D ε A -> C ε D)) /\ 
                            (forall C, C ε A  -> C ε a)) -> A ε a.
Proof.
apply isEpsilon. 
Qed. 

(* If A is something, then A is a singular *)
Lemma OntoT5 : forall A b, A ε b -> A ε A.
Proof.
intros A b H.
assert (H1:=H).
apply OntoT4 with (A:=A)(a:=A).
apply OntoT1 with (A:=A)(a:=b) in H.
split.
assumption.
split.
apply OntoT2 with (A:=A)(a:=b).
assert (H2:=H1).
assumption.
apply OntoT0 with (A:=A)(a:=b).
assumption.
Qed.

(* characteristic thesis of the ontology *)
Lemma OntoT6 : forall A B a, A ε B /\ B ε a -> B ε A.
Proof.
intros A B a H.
destruct H as (H1, H2).
assert (H3 := H2).
apply OntoT5 in H2. 
apply OntoT2 with (C:=B)(D:=A) in H3.
assumption.
split; assumption.
Qed.

Lemma OntoT7 : forall A B a, A ε B /\ B ε a -> A ε a.
Proof.
intros A B a H0.
decompose [and] H0.
apply isEpsilon in H1.
decompose [and] H1.
apply H5 with (C:=A).
assumption.
Qed.

(* contradictory name *)
Lemma OntoT8 : forall A, A ε empty -> ~(A ε empty).
Proof.
intros A H.
assert (H':=H).
apply empty_equi in H'.
unfold empty_name in H'.
decompose [and] H'.
contradiction.
Qed.

(* empty name is not a singular *)
Lemma OntoT9 : empty ε empty -> ~(empty ε empty).
Proof.
apply OntoT8.
Qed. 

(* it is false that any name is a singular - creativity *)

Lemma OntoT10 : ~ forall A, A ε A.
Proof.
intro H.
specialize H with (A:=empty).
assert (H':=H).
apply OntoT9 in H.
contradiction.
Qed.

Lemma OntoT12 : forall A b, A ε (distinct b) -> ~(A ε b).
Proof.
intros A b H.
assert (H':=H).
apply (distinct_equi A b) in H.
unfold distinct_from in H.
decompose [and] H.
assumption.
Qed. 

Lemma OntoT21 : forall A B a, A ε B /\ B ε a -> singular_equality A B.
Proof.
intros A B a H1.
decompose [and] H1.
apply OntoT6 in H1.
unfold singular_equality.
split; assumption.
Qed.

Lemma OntoT23 : reflexive _ weak_equality.
Proof.
intro a.
unfold weak_equality.
intro A.
reflexivity.
Qed.

Lemma OntoT24 : symmetric _ weak_equality.
Proof.
intros a b.
unfold weak_equality.
intro H.
symmetry.
revert A.
exact H.
Qed. 

Lemma OntoT25 : transitive _ weak_equality.
Proof.
unfold weak_equality.
intros a b c H H' A.
specialize (H A).
specialize (H' A).
destruct H as (H1, H2).
destruct H' as (H3, H4).
split; auto.
Qed.

Notation "a ≡≡≡ b" := (weak_equality a b)  (at level 30).

Add Parametric Relation  : N (weak_equality)
 reflexivity proved by (OntoT23)
 symmetry proved by (OntoT24)
 transitivity proved by (OntoT25)
as eq_N.

Lemma OntoT27 : symmetric _ singular_equality.
Proof.
intros A B H0.
destruct H0.
unfold singular_equality.
split; assumption.
Qed.

Lemma OntoT28 : transitive _ singular_equality.
Proof.
intros A B C H H'.
destruct H.
destruct H'.
unfold singular_equality.
split; [ apply isEpsilon in H1;decompose [and] H1; apply H6 with (C0:=A); assumption |
apply isEpsilon in H0;decompose [and] H0; apply H6 with (C:=C); assumption ].
Qed.

Class Morphism_N (g : N->Prop) : Type := 
            compat_N : forall (y1 y2: N), (y1 ≡≡≡ y2) -> ((g y1) ≡≡ (g y2)).

Add Parametric Morphism (g : N->Prop)(M : Morphism_N g) :
            g with signature (@weak_equality ==> @iff) as extensional_N.
Proof. 
intros.
apply compat_N.
assumption.
Qed.

Lemma N_rewrite (h:N->Prop)(t:Morphism_N h) : forall a b, (a ≡≡≡ b) -> (@h a ≡≡ @h b).
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Lemma OntoT28' : forall A B C, singular_equality A B /\ singular_equality B C -> singular_equality A C.
Proof.
intros.
decompose [and] H.
destruct OntoT28 with (x:=A)(y:=B)(z:=C).
assumption.
assumption.
unfold singular_equality.
split; assumption.
Qed.

Lemma OntoT29 : forall A B, (singular_equality A B -> weak_equality A B).
Proof. 
intros A B H.
unfold singular_equality in H.
destruct H.
red.
intros.
red.
split.
intro H2.
apply OntoT7 with (A:=A0)(B:=A)(a:=B).
split; [assumption | assumption].
intro H1.
apply OntoT7 with (A:=A0)(B:=B)(a:=A).
split; assumption.
Qed. 

(* ====================== MEREOLOGICAL DEFINITIONS & AXIOMS ============================= *)

Parameter pt : N -> N.
Parameter el : N -> N.
Parameter Kl : N -> N.
                        
(* for manipulation of a single term = alias *)
Definition PartOf         := fun A B => A ε (pt B).

Axiom asymmetric_Part     : forall A B, A ε (pt B) -> B ε (distinct (pt A)). (*A1*)
Axiom transitive_Part     : Transitive PartOf.  (*A2*)

Definition elementOf      := fun A B => A ε A /\ (singular_equality A B \/ PartOf A B). (*D1*)
Parameter elem_equi       : forall A B, A ε (el B) ≡≡ elementOf A B.

Definition klassOf        := fun A a => (A ε A /\ (exists B, B ε a) /\ (forall B, B ε a -> B ε (el A)) /\ 
                                 (forall B, B ε (el A) -> exists C D, (C ε a /\ D ε (el C) /\ D ε (el B)))).
Parameter klass_equi      : forall A a, A ε (Kl a) ≡≡ klassOf A a.
 
Axiom klass_uniqueness    : forall A B a, (A ε (Kl a) /\ B ε (Kl a)) -> (singular_equality A B).
Axiom klass_existence     : forall A a, A ε a -> exists B, B ε (Kl a).  
                          
(* =========================== MEREOLOGICAL THEOREMS ========================== *)

Definition Phi (E1:N->N->Prop)(E2:N)(E3:N->N)(E4:N) := E1 E2 (E3 E4). 

Lemma MereoT1 : forall A a, A ε (Kl a) -> A ε A.
Proof.
intros A a H.
apply (klass_equi A a) in H.
unfold klassOf in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT2 : forall A a, A ε (Kl a) -> exists B, B ε a.
Proof.
intros A a H.
apply (klass_equi A a) in H.
unfold klassOf in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT3 : forall A a, A ε (Kl a) -> forall B, B ε a -> B ε (el A).
Proof.
intros A a H.
apply (klass_equi A a) in H.
unfold klassOf in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT4 : forall A a, A ε (Kl a) -> forall B, B ε (el A) -> exists C D, (C ε a /\ D ε (el C) /\ D ε (el B)).
Proof.
intros A a H.
apply (klass_equi A a) in H.
unfold klassOf in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT5 : forall A:N, PartOf A A -> ~PartOf A A.
Proof.
intro A.
unfold PartOf.
intro H.
apply asymmetric_Part with (A:=A)(B:=A) in H.
assert (H':=H).
apply (distinct_equi A (pt A)) in H.
unfold distinct_from in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT6 : forall A a:N, A ε a -> A ε (el A).
Proof.
intros A a H0.
apply OntoT5 in H0.
assert (H1 := H0).
apply LO01 in H0.
apply Proto01 with (P:=singular_equality A A)(Q:=PartOf A A) in H0.
assert (H2: (A ε A /\ (singular_equality A A \/ PartOf A A))).
split; assumption.
apply elem_equi.
unfold elementOf.
assumption.
Qed.

Lemma MereoT7 : forall A, A ε A -> A ε (el A).
Proof.
intro A.
apply MereoT6 with (a:=A).
Qed. 

Lemma MereoT8 : forall A a, A ε (Kl a) ->  A ε (el A).
Proof.
intros A a H.
apply MereoT6 with (a:=(Kl a)).
assumption.
Qed.

Lemma MereoT9 : forall A B:N, A ε (el B) -> B ε B.
Proof.
intros A B H.
assert (H' := H).
apply OntoT5 in H'.
apply elem_equi in H.
unfold elementOf in H.
decompose [and] H.
decompose [or] H1.
unfold singular_equality in H2.
decompose [and] H2.
apply OntoT5 with (A:=B)(b:=A) in H4.
assumption.
apply asymmetric_Part  with (A:=A)(B:=B) in H2.
apply (distinct_equi B (pt A)) in H2.
unfold distinct_from in H2.
decompose [and] H2.
assumption.
Qed.

Lemma MereoT10 : forall A a, A ε a ->  A ε (Kl A).
Proof.
intros A a H0.
apply klass_equi.
unfold klassOf.
assert (H1:=H0).
apply (OntoT5 A a) in H0.
split. assumption.
split. exists A. assumption.
split. intros B H2. apply elem_equi. unfold elementOf. assert (H3:=H2). apply OntoT5 in H2. 
split. assumption. 
left. unfold singular_equality. 
split. assumption. apply OntoT6 with (A:=B)(B:=A)(a:=A).  
split; assumption. 
intros B H3.
exists A, B.
split. assumption.
split. assumption.
apply OntoT5 with (A:=B)(b:=el A) in H3. 
apply MereoT7 in H3.
assumption.
Qed.

Lemma MereoT11 : forall A, A ε A ->  A ε (Kl A).
Proof.
intro A.
apply (MereoT10 A A).
Qed.

Lemma MereoT12 : forall A, (A ε A) ≡≡ (A ε (Kl A)).
Proof.
intro A.
split; [apply MereoT11 | apply MereoT1].
Qed.

Lemma MereoT13 : forall A a, (A ε a) -> (Kl a) ε Kl a.
Proof.
intros A a H1.
apply isEpsilon with (A:=Kl a)(a:=Kl a).
split. apply (klass_existence A a). assumption.
split.
intros C D H2.
apply klass_uniqueness in H2.
unfold singular_equality in H2.
decompose [and] H2.
assumption.
intros B H2.
assumption.
Qed.

Lemma MereoT15 : forall B C, (B ε C /\ C ε B) -> (weak_equality B C).
Proof.
intros B C H.
decompose [and] H.
intro A.
split; [ intro H2; apply OntoT7 with (A:=A)(B:=B)(a:=C); split; assumption |
intro H2; apply OntoT7 with (A:=A)(B:=C)(a:=B); split; assumption ].
Qed.

Lemma MereoT17 : forall A B C, PartOf A B /\ singular_equality B C -> PartOf A C.
Proof.
intros A B C H.
destruct H.
apply OntoT29 in H0.
unfold PartOf in H.
unfold PartOf.
apply symmetry in H0.
evar (H3:Morphism_N (Phi epsilon A pt)).
apply (N_rewrite (Phi epsilon A pt) H3) in H0.
unfold Phi in H0.
rewrite H0.
assumption.
Grab Existential Variables.
admit.
Qed.

Lemma MereoT18 : forall A B C, A ε (el B) /\ singular_equality B C -> A ε (el C).
Proof.
intros A B C H.
destruct H as [H1 H2].
apply OntoT29 in H2.
apply symmetry in H2.
evar (H3:Morphism_N (Phi epsilon A el)).
apply (N_rewrite (Phi epsilon A el) H3) in H2.
unfold Phi in H2.
rewrite H2.
assumption.
Grab Existential Variables.
admit.
Qed.

Lemma MereoT19 : forall A B C, PartOf A B /\ singular_equality A C -> PartOf C B.
Proof.
intros A B C H.
decompose [and] H.
destruct H1. 
unfold PartOf in H0. 
apply OntoT7 with (A:=C)(B:=A)(a:=pt B). 
split; assumption.
Qed.

Lemma MereoT22 : forall A a, A ε a -> A ε (el (Kl a)).
Proof.
intros A a H.
apply MereoT3 with (a:=a)(A:=Kl a)(B:=A); 
[ apply MereoT13 with (A:=A)(a:=a); assumption | assumption].
Qed.

Lemma MereoT23 : forall A B a, (A ε (Kl B) /\ B ε a) -> singular_equality A B.
Proof.
intros A B a H.
decompose [and] H.
apply OntoT5 in H1.
apply MereoT11 in H1.
apply klass_uniqueness with (a:=B).
split; assumption.
Qed.

Lemma MereoT24 : forall A a, (A ε Kl a) -> singular_equality A (Kl a).
Proof.
intros A a H1.
apply OntoT21 with (A:=A)(B:=Kl a)(a:=Kl a).
split; [assumption | apply (MereoT13 A); apply MereoT2 in H1; intuition auto ].
Qed.

Lemma MereoT25 : forall a, exist_at_least a ≡≡ exist_at_least (Kl a).
Proof.
intro a.
split.
intro H1.
unfold exist_at_least in H1.
elim H1.
intros A H2.
apply klass_existence in H2.
change (exists B : N, B ε Kl a) with (exist_at_least (Kl a)) in H2.
assumption.
intro H1.
unfold exist_at_least in H1.
elim H1.
intros A H2.
apply MereoT2 in H2.
change (exists B : N, B ε a) with (exist_at_least a) in H2.
assumption.
Qed.


(* =========================== Partial Order ============================== *) 

Lemma Reflexive_ElementOf : forall A, A ε A -> A ε (el A). (* reflexivity Th21 *)
Proof.
intros A H1. 
apply MereoT6 with (A:=A)(a:=A) in H1.
assumption.
Qed.

Lemma AntiSymmetric_ElementOf : forall A B, A ε (el B) /\ B ε (el A) -> singular_equality A B.
Proof.
intros A B H0.
destruct H0 as [H1 H2].
assert (G1:=H1).
assert (G2:=H2).
apply MereoT9 in G1.
apply MereoT9 in G2.
apply (elem_equi A B) in H1.
apply (elem_equi B A) in H2. 
unfold elementOf in H1.
unfold elementOf in H2.
decompose [and] H1.
decompose [and] H2.
elim H0.
trivial.
intro H5.
apply asymmetric_Part in H5.
apply distinct_equi in H5.
unfold distinct_from in H5.
decompose [and] H5.
elim H4.
intro H8.
apply OntoT27. 
assumption.
intro H9.
unfold PartOf in H9.
contradiction.
Qed. 
(* Th20 p408 *)
Lemma Transitive_ElementOf : forall A B C, A ε (el B) /\ B ε (el C) -> A ε (el C).
Proof.
intros A B C H.
destruct H as [H2 H3].
assert (G2:=H2).
assert (G3:=H2).
apply MereoT9 in G2.
apply OntoT5 in G3.
apply elem_equi in H2.
unfold elementOf in H2.
destruct H2.
apply elem_equi in H3.
unfold elementOf in H3.
destruct H3.
apply elem_equi.
unfold elementOf.
split.
assumption.
decompose [or] H0.
decompose [or] H2.
left.
apply OntoT28' with (A:=A)(B:=B)(C:=C).
split.
assumption.
assumption.
right.
apply MereoT19 with (A:=B)(B:=C)(C:=A).
split.
assumption.
apply OntoT27.
assumption.
decompose [or] H2.
right.
apply MereoT17 with (A:=A)(B:=B)(C:=C).
split.
assumption.
assumption.
right.
apply transitivity with (x:=A)(y:=B)(z:=C).
assumption.
assumption. 
Qed. 


(* ================== EXAMPLE ======================= *)

(*Typeclasses eauto := debug. *)

Variables A1 A2 A3 A4 A5 A6 A7 A a P S  :N.

(* singulars *)

Hypotheses (A1_is_A1 : A1 ε A1)
           (A2_is_A2 : A2 ε A2)
           (A3_is_A3 : A3 ε A3)
           (A4_is_A4 : A4 ε A4)
           (A5_is_A5 : A5 ε A5)
           (A6_is_A6 : A6 ε A6)
           (A7_is_A7 : A7 ε A7)
           (P_is_P   : P ε P)
           (S_is_S   : S ε S)

(* basic knowledge *)
           (A1_is_a : A1 ε a)
           (A2_is_a : A2 ε a)
           (A3_is_a : A3 ε a)
           (A4_is_a : A4 ε a)
           (A5_is_a : A5 ε a)
           (A6_is_a : A6 ε a)
           (A7_is_a : A7 ε a)
           (P_is_A3 : P ε A3) 

           (Apt1 :  A1 ε (pt A))
           (Apt2 :  A2 ε (pt A))
           (Apt3 :  A3 ε (pt A))
           (Apt4 :  A4 ε (pt A))
           (Apt5 :  A5 ε (pt A))
           (Apt6 :  A6 ε (pt A))
           (Apt7 :  A7 ε (pt A))

(****************   el ****************)

           (Ael1 : A1 ε (el A))
           (Ael2 : A2 ε (el A))
           (Ael3 : A3 ε (el A))
           (Ael4 : A4 ε (el A))
           (Ael5 : A5 ε (el A))
           (Ael6 : A6 ε (el A))
           (Ael7 : A7 ε (el A))
           (Ael8 : P ε (el A3))

           (Akl01 :  A ε (Kl a)).

Create HintDb Torus.

Hint Resolve A1_is_A1 A2_is_A2 A3_is_A3 A4_is_A4 A5_is_A5 A6_is_A6 A7_is_A7 P_is_P S_is_S 
             A1_is_a A2_is_a A3_is_a A4_is_a A5_is_a A6_is_a A7_is_a P_is_A3 
             Apt1 Apt2 Apt3 Apt4 Apt5 Apt6 Apt7 Ael1 Ael2 Ael3 Ael4 Ael5 Ael6 Ael7 Ael8 Akl01 : Torus.



Lemma AelTrans : P ε (el A3) /\ A3 ε (el A) -> P ε (el A).
Proof.
intro H.
apply Transitive_ElementOf in H.
auto.
Qed.

(****************   ProofEl ****************)

Lemma prooEL01 : A1 ≡≡≡ A \/ A1 ε (pt A) .
Proof.
right.
auto with Torus.
Qed.

Lemma prooEL02 :  A2 ≡≡≡ A \/ A2 ε (pt A).
Proof.
right.
auto with Torus.
Qed.

Lemma prooEL03 :  A3 ≡≡≡ A \/ A3 ε (pt A).
Proof.
right.
auto with Torus.
Qed.

Lemma prooEL04 : A4 ≡≡≡ A \/ A4 ε (pt A).
Proof.
right.
auto with Torus.
Qed.

Lemma prooEL05 : A5 ≡≡≡ A \/ A5 ε (pt A).
Proof.
right.
auto with Torus.
Qed.

Lemma prooEL06 : A6 ≡≡≡ A \/ A6 ε (pt A).
Proof.
right.
auto with Torus.
Qed.

Lemma prooEL07 :  A7 ≡≡≡ A \/ A7 ε (pt A).
Proof.
right.
auto with Torus.
Qed.

(****************   Klass proof  ****************)

Hint Resolve isEpsilon.

Lemma  P_el_A_1 : A3 ε a. 
Proof.
auto with Torus.
Qed.

Lemma  P_el_A_2 : P ε (el A3).
Proof.
auto with Torus.
Qed.

Lemma  P_el_A_3 : P ε (el P).
Proof.
apply Reflexive_ElementOf.
auto with Torus.
Qed.

Lemma Akl03 : P ε (el A) -> A3 ε a /\ P ε (el A3) /\ P ε (el P).
intros H.
split.
auto with Torus.
split.
auto with Torus.
apply Reflexive_ElementOf.
auto with Torus.
Qed.
(*
Lemma Akl04 : S ε (el A) -> _ ε a /\ S ε (el _) /\ S ε (el S).
Proof.
intros H.
split.
Focus 2.
split.
apply Reflexive_ElementOf.
auto with Torus.
apply Reflexive_ElementOf.
auto with Torus.
auto with Torus. (* unable to find the matching proof *)
Show.
Abort. 
*) 

End Mereology.






