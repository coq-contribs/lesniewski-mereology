Require Import Coq.Init.Tactics.
Require Import Relation_Definitions.
Require Import Coq.Program.Basics.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Structures.Equalities.
Require Export Relation_Definitions.
Require Import Relation_Definitions Setoid.
Require Import Coq.Classes.Morphisms.

Module Mereology.

(************************** Basic Lemmas ***************************)

Notation "a ≡≡ b" := (iff a b)  (at level 70).

Structure Morphism  : Type := {
  f       :> Prop -> Prop;
  compat  : forall (x1 x2: Prop), (x1 ≡≡ x2) -> ((f x1) ≡≡ (f x2))}.

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



(* ====================== ONTOLOGICAL AXIOM  ============================= *)

Class N : Type.

Class epsilon (A a:N) : Prop.
(* explication p 283 -> no typing on singulars and plurals *)
Notation "A 'ε' b" := (epsilon A b)  (at level 70). 

Axiom isEpsilon : forall A a, A ε a ≡≡ ((exists B, B ε A) /\ 
                              (forall C D, (C ε A /\ D ε A) -> C ε D) /\
                              (forall C, C ε A  -> C ε a)).

(* ==================================== ONTOLOGICAL DEFINITIONS =============================== *)

Parameter exist_at_least      : N -> Prop.
Parameter D1                  : forall a, exist_at_least a ≡≡ exists A, A ε a. (* D1 *) 

Parameter exist_at_most       : N -> Prop.
Parameter D2                  : forall a:N, exist_at_most a ≡≡ forall B C, B ε a /\ C ε a -> B ε C. (* D2 *) 

Parameter exist_exactly       : N -> Prop.
Parameter D3                  : forall A, exist_exactly A ≡≡ forall b, A ε b. (* D3 *)

Parameter singular_equality   : N -> N -> Prop.
Parameter D4                  : forall A B,  singular_equality A B ≡≡ (A ε B /\ B ε A). (* D4 *)

Parameter singular_difference : N -> N -> Prop.
Parameter D5                  : forall A B, singular_difference A B ≡≡ (A ε A /\ B ε B /\ ~singular_equality A B). (* D5 *)

Parameter weak_equality       : N -> N -> Prop.
Parameter D6                  : forall a b,  weak_equality a b ≡≡ (forall A, (A ε a) ≡≡ (A ε b)). (* D6 *)

Parameter strong_equality     : N -> N -> Prop.
Parameter D7                  : forall a b, strong_equality a b ≡≡ ((exists G, G ε a) /\ forall G, (G ε a) ≡≡ (G ε b)). (* D7 *)

Parameter weak_inclusion      : N -> N -> Prop.
Parameter D8                  : forall a b, weak_inclusion a b ≡≡ forall A, A ε a -> A ε b. (* D8 *)

Parameter strong_inclusion    : N -> N -> Prop.
Parameter D9                  : forall a b, strong_inclusion a b ≡≡ ((exists G, G ε a) /\ forall G, G ε a -> G ε b). (* D9 *)

Parameter partial_inclusion   : N -> N -> Prop.
Parameter D10                 : forall a b, partial_inclusion a b ≡≡ exists G, (G ε a /\ G ε b). (* D10 *)

Parameter empty               : N.
Parameter D13                 : forall A, A ε empty ≡≡ (A ε A /\ ~(A ε A)). (* D13 *)

Parameter universal           : N.
Parameter D14                 : forall A, A ε universal ≡≡ (A ε A).  (* D14 *)

Parameter distinct            : N -> N.
Parameter D15                 : forall A b, A ε (distinct b) ≡≡ (A ε A /\ ~(A ε b)). (*D15*)

Parameter meet                : N -> N -> N.
Parameter D16                 : forall A a b,  A ε (meet a b) ≡≡ (A ε A /\ (A ε a) /\ (A ε b)).  (*D16*)

(* =========================== ONTOLOGICAL THEOREMS =============================== *)

Class Antisymmetric  (R:relation N) :=
      antisymmetry : forall a b, R a b /\ R b a -> singular_equality a b.

Class Reflexive  (R:relation N) :=
      reflexivity : forall A, A ε A -> R A A.

Class Transitive  (R:relation N) :=
      transitivity : forall A B C, R A B /\ R B C -> R A C.

Class POrder (R:relation N) := {
   por_refl    :> Reflexive R;
   por_antisym :> Antisymmetric R;
   por_trans   :> Transitive R}.

Lemma L001 : forall A, A ε A -> singular_equality A A.
Proof.
intros A H1.
apply D4.
split; assumption.
Qed.

Lemma L002 : forall P Q:Prop, P -> P \/ Q.
Proof.
intros.
left.
assumption.
Qed.

Lemma OntoT0 : forall A a, A ε a -> (forall C, C ε A -> C ε A).
Proof.
intros.
assumption.
Qed.

Lemma OntoT1 : forall A a, A ε a -> exists B, B ε A.
Proof.
intros A a H0.
apply isEpsilon in H0.
decompose [and] H0.
assumption.
Qed.

Lemma OntoT2 : forall A a, A ε a -> (forall C D, (C ε A /\ D ε A) -> C ε D).
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
                            (forall C, C ε A  -> C ε a)) 
                              ->  A ε a.
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
apply D13 in H.
decompose [and] H.
red.
contradiction.
Qed.

(* empty name is not a singular *)
Lemma OntoT9 : empty ε empty -> ~(empty ε empty).
Proof.
apply OntoT8.
Qed. 

(* it is false that any name is a singular - creativity *)

Lemma OntoT10 : ~forall A, A ε A.
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
apply D15 in H.
decompose [and] H.
assumption.
Qed.

Lemma OntoT17 : ~exist_at_least empty.
Proof.
red.
intro H.
apply D1 in H.
elim H.
intros A H1.
assert (H2:=H1).
apply OntoT8 in H2.
contradiction.
Qed.

Lemma OntoT21 : forall A B a, A ε B /\ B ε a -> singular_equality A B.
Proof.
intros A B a H1.
decompose [and] H1.
apply OntoT6 in H1.
apply D4.
split; assumption.
Qed.

Lemma OntoT23 : reflexive _ weak_equality.
Proof.
intro a.
apply D6.
intro A.
reflexivity.
Qed.

Lemma OntoT24 : symmetric _ weak_equality.
Proof.
intros a b W.
apply D6.
intro A.
apply D6 with (a:=a)(b:=b)(A:=A) in W.
symmetry.
assumption.
Qed. 

Lemma OntoT25 : transitive _ weak_equality.
Proof.
intros a b c H H'.
apply D6.
intro A.
apply D6 with (a:=a)(b:=b)(A:=A) in H.
apply D6 with (a:=b)(b:=c)(A:=A) in H'.
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
apply D4.
apply D4 in H0.
decompose [and] H0.
split; assumption.
Qed.

Lemma OntoT28 : transitive _ singular_equality.
Proof.
intros A B C H H'.
apply D4.
apply D4 in H.
apply D4 in H'.
destruct H.
destruct H'.
split; [ apply isEpsilon in H1; decompose [and] H1; apply H6 with (C0:=A); assumption |
  apply isEpsilon in H0; decompose [and] H0; apply H6 with (C:=C); assumption ].
Qed. 

Lemma OntoT28' : forall A B C, singular_equality A B /\ singular_equality B C -> singular_equality A C.
Proof.
intros.
decompose [and] H.
apply OntoT28 with (x:=A)(y:=B)(z:=C).
assumption.
assumption.
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

Lemma N_rewrite (h:N->Prop)(t:Morphism_N h) : forall (a b:N), (a ≡≡≡ b) -> (@h a ≡≡ @h b).
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Lemma OntoT29 : forall A B, (singular_equality A B -> weak_equality A B).
Proof. 
intros A B H.
apply D4 in H.
destruct H.
apply D6.
split.
intro H1.
apply OntoT7 with (A:=A0)(B:=A)(a:=B).
split; assumption.
intro H2.
apply OntoT7 with (A:=A0)(B:=B)(a:=A).
split; assumption.
Qed. 

(* ====================== MEREOLOGICAL DEFINITIONS & AXIOMS ============================= *)

Parameter pt       : N -> N.
Parameter el       : N -> N.
Parameter Kl       : N -> N.
Parameter coll     : N -> N.   
Parameter subcoll  : N -> N.   
Parameter ext      : N -> N.    
Parameter compl    : N -> N -> N. 
Parameter ov       : N -> N.   
Parameter union    : N -> N -> N. 
Parameter discrete : N -> Prop.
Parameter U        : N.

(* for manipulation of a single term = alias *)
Definition Part_of           := fun A B => A ε pt B.

Axiom asymmetric_Part        : forall A B, A ε pt B -> B ε (distinct (pt A)). (*A1*)
Axiom transitive_Part        : Transitive Part_of.  (*A2*)

Parameter MD1                : forall A B, A ε el B ≡≡ (A ε A /\ (singular_equality A B \/ Part_of A B)).

Parameter MD2                : forall A a, A ε Kl a ≡≡ (A ε A /\ 
                                                        (exists B, B ε a) /\ 
                                                        (forall B, B ε a -> B ε el A) /\ 
                                 (forall B, B ε el A -> exists C D, (C ε a /\ D ε el C /\ D ε el B))).
 
Axiom klass_uniqueness       : forall A B a, (A ε Kl a /\ B ε Kl a) -> singular_equality A B.
Axiom klass_existence        : forall A a, A ε a -> exists B, B ε Kl a.

(* P is a collection of a *)
Parameter MD3                : forall P a, P ε coll a ≡≡ (P ε P /\ forall Q, Q ε el P -> exists C D, 
                                      (C ε a /\ C ε el P /\ D ε el C /\ D ε el Q)).

(* P is a sub-collection of Q *)
Parameter MD4                : forall P Q, P ε subcoll Q ≡≡ (P ε P /\ forall C, (C ε el P -> C ε el Q)).

(* P is a external to Q *)
Parameter MD5                : forall P Q, P ε ext Q ≡≡ (P ε P /\ ~(exists C, (C ε el P /\ C ε el Q))).

(* P is a complement of Q relative to collection R *)
Parameter MD6                : forall P Q R, P ε compl Q R ≡≡ (P ε P /\ Q ε subcoll R /\ P ε (Kl (meet (el R)(ext Q)))).

(* P and Q overlap *)
Parameter MD7                : forall P Q, P ε ov Q ≡≡ (P ε P /\ exists C, (C ε el P /\ C ε el Q)).

(* The a's are discrete  *)
Parameter MD8                :  forall a, discrete a ≡≡ forall P Q, (P ε a /\ Q ε a) -> singular_equality P Q \/ P ε ext Q. (*MD8*)

(* A is the universe *)
Parameter MD9                : forall A, A ε U ≡≡ (A ε Kl universal). 

(* A belongs to the union of a and b *)
Parameter MD10               : forall A a b, A ε (union a b) ≡≡ (A ε A /\ (A ε a \/ A ε b)).
                             
(* =========================== MEREOLOGICAL THEOREMS ========================== *)


(* allow to define appropriate structures for use of N_rewrite, the last argument must be
 the variable that is involved in the  weak_equality a ≡≡≡ b *)

Definition Psi (E1:N->N->Prop)(E2:N)(E3:N->N)(E4:N) := E1 E2 (E3 E4). 
Definition Psi' (E1:N->N->Prop)(E3:N->N)(E4:N->N)(E5:N)(E2:N) := E1 E2 (E3 (E4 E5)). 
Definition Psi'' (E1:N->N->Prop)(E3:N->N)(E5:N)(E2:N) := E1 E2 (E3 E5). 
Definition Phi (E1:N->N->Prop)(E2:N)(E3:N->N)(E4:N) := E1 E2 (E3 E4). 

Lemma MereoT1 : forall a A, A ε Kl a -> A ε A.
Proof.
intros A a H.
apply MD2 in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT2 : forall a A :N, A ε Kl a -> exists B, B ε a.
Proof.
intros A a H.
apply MD2 in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT3 : forall A a, A ε Kl a -> forall B, (B ε a -> B ε el A).
Proof.
intros A a H.
apply MD2 in H.
decompose [and] H.
assumption.
Qed.

Lemma MereoT4 : forall A B a, A ε Kl a -> B ε el A -> exists C D, (C ε a /\ D ε el C /\ D ε el B).
Proof.
intros A B a H.
apply MD2 in H.
decompose [and] H.
specialize (H4 B).
assumption.
Qed.

Lemma MereoT5 : forall A, ~Part_of A A.
Proof.
red.
intros A H.
unfold Part_of in H.
assert (H':=H).
apply asymmetric_Part with (A:=A)(B:=A) in H.
apply D15 with (A:=A)(b:=(pt A)) in H. 
decompose [and] H.
contradiction.
Qed.

Lemma MereoT6 : forall A a, A ε a -> A ε el A.
Proof.
intros A a H0.
apply OntoT5 in H0.
assert (H1 := H0).
apply L001 in H0.
apply L002 with (P:=singular_equality A A)(Q:=Part_of A A) in H0.
assert (H2: (A ε A /\ (singular_equality A A \/ Part_of A A))).
split; assumption.
apply MD1.
assumption.
Qed.

Lemma MereoT7 : forall A, A ε A -> A ε el A.
Proof.
intro A.
apply MereoT6 with (a:=A).
Qed. 

Lemma MereoT8 : forall A a, A ε Kl a ->  A ε el A.
Proof.
intros A a H.
apply MereoT6 with (a:=(Kl a)).
assumption.
Qed.

Lemma MereoT9 : forall A B, A ε el B -> B ε B.
Proof.
intros A B H.
assert (H' := H).
apply OntoT5 in H'.
apply MD1 in H.
decompose [and] H.
decompose [or] H1.
apply D4 in H2.
decompose [and] H2.
apply OntoT5 with (A:=B)(b:=A) in H4.
assumption.
apply asymmetric_Part  with (A:=A) (B:=B) in H2.
apply OntoT5 with (A:=B)(b:=(distinct (pt A))) in H2.
assumption.
Qed.  

Lemma MereoT10 : forall A a, A ε a ->  A ε Kl A.
Proof.
intros A a H0.
apply MD2.
assert (H1:=H0).
apply (OntoT5 A a) in H0.
split. assumption.
split. exists A. assumption.
split. intros B H2. apply MD1. assert (H3:=H2). apply OntoT5 in H2. 
split. assumption. 
left. apply D4. 
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

Lemma MereoT11 : forall A, A ε A ->  A ε Kl A.
Proof.
intro A.
apply (MereoT10 A A).
Qed.

Lemma MereoT12 : forall A, A ε A ≡≡ (A ε Kl A).
Proof.
intro A.
split; [apply MereoT11 | apply MereoT1].
Qed.

Lemma MereoT13 : forall A a, A ε a -> Kl a ε Kl a.
Proof.
intros A a H1.
apply isEpsilon with (A:=Kl a)(a:=Kl a).
split. apply (klass_existence A a). assumption.
split.
intros C D H2.
apply klass_uniqueness in H2.
apply D4 in H2.
decompose [and] H2.
assumption.
intros B H2.
assumption.
Qed.

Lemma MereoT15 : forall B C, (B ε C /\ C ε B) -> weak_equality B C.
Proof.
intros B C H.
decompose [and] H.
apply D6.
split; [ intro H2; apply OntoT7 with (A:=A)(B:=B)(a:=C); split; assumption |
intro H2; apply OntoT7 with (A:=A)(B:=C)(a:=B); split; assumption ].
Qed.

Lemma MereoT16 : forall (A:N)(B:N)(C:N)(Phi:N->N), A ε Phi B /\ singular_equality B C -> A ε Phi C.
Proof.
intros A B C phi H.
decompose [and] H.
apply OntoT29 in H1.
apply symmetry in H1.
evar (H3:Morphism_N (Psi epsilon A phi)).
apply (N_rewrite (Psi epsilon A phi) H3) in H1.
unfold Psi in H1.
rewrite H1.
assumption.
Grab Existential Variables.
admit.
Qed. 

Lemma MereoT17 : forall A B C,  Part_of A B /\ singular_equality B C -> Part_of A C.
Proof.
intros A B C.
apply MereoT16 with (A:=A)(B:=B)(C:=C)(Phi:=pt).
Qed.

Lemma MereoT18 : forall A B C, A ε el B /\ singular_equality B C -> A ε el C.
Proof.
intros A B C.
apply MereoT16 with (A:=A)(B:=B)(C:=C)(Phi:=el).
Qed.

Lemma MereoT19 : forall A B C, Part_of A B /\ singular_equality A C -> Part_of C B.
Proof.
intros A B C H.
decompose [and] H.
apply D4 in H1.
unfold Part_of in H0. 
apply OntoT7 with (A:=C)(B:=A)(a:=pt B). 
decompose [and] H1.
split; assumption.
Qed.

Lemma MereoT22 : forall A a, A ε a -> A ε el (Kl a).
Proof.
intros A a H.
apply MereoT3 with (a:=a)(A:=Kl a)(B:=A); 
[ apply MereoT13 with (A:=A)(a:=a); assumption | assumption].
Qed.

Lemma MereoT23 : forall A B a, (A ε Kl B /\ B ε a) -> singular_equality A B.
Proof.
intros A B a H.
decompose [and] H.
apply OntoT5 in H1.
apply MereoT11 in H1.
apply klass_uniqueness with (a:=B).
split; assumption.
Qed.

Lemma MereoT24 : forall A a, A ε Kl a -> singular_equality A (Kl a).
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
apply D1 in H1.
elim H1.
intros A H2.
apply klass_existence in H2.
apply D1 in H2.
assumption.
intro H1.
apply D1 in H1.
elim H1.
intros A H2.
apply MereoT2 in H2.
apply D1 in H2.
assumption.
Qed.

(* Theorems 26 and 27 show that in mereology, the class of a and the class of the class of a
 stand for the same object, which is in contrast with set theory *)

Lemma MereoT26 : forall A a, A ε Kl a -> A ε Kl (Kl a).
Proof.
intros A a H0.
assert (H1:=H0).
assert (H2:=H0).
apply klass_existence in H1.
elim H1.
intros B H3. clear H1.
apply MereoT24 in H2. 
apply OntoT27 in H2.
assert (H4 :B ε Kl (Kl a) /\ singular_equality (Kl a) A).
split; assumption.
apply MereoT16 with (A:=B)(B:=Kl a)(C:=A) in H4.
assert (H5 :B ε Kl A /\ A ε Kl a).
split; assumption.
apply MereoT23 with (A:=B)(B:=A)(a:=Kl a) in H5.
apply OntoT29 in H5.
evar (H6 :Morphism_N (Psi' epsilon Kl Kl a)).
apply (N_rewrite (Psi' epsilon Kl Kl a) H6) in H5.
unfold Psi' in H5.
rewrite H5 in H3.
assumption.
Grab Existential Variables.
admit.
Qed.

Lemma MereoT27 : forall A a, A ε Kl (Kl a) -> A ε Kl a.
Proof.
intros A a H0.
assert (H1:=H0).
assert (H2:=H0).
apply MereoT6 in H0.
apply MereoT4 with (A:=A)(B:=A)(a:=Kl a) in H1.
Focus 2. assumption.
elim H1.
intros C H.
elim H.
clear H H1.
intros D H1.
destruct H1 as [H4 H5].
assert (H6:=H4).
assert (H7:=H4).
clear H5.
apply MereoT24 in H4.
apply OntoT27 in H4.
assert (H3 :(A ε Kl (Kl a) /\ singular_equality (Kl a) C)).
split; assumption.
apply MereoT16 with (A:=A)(B:=Kl a)(C:=C)(Phi:=Kl) in H3.
apply OntoT5 in H6.
assert (H5 :(A ε Kl C /\ C ε C)).
split; assumption.
apply MereoT23 in H5. clear H6.
apply OntoT29 in H5.
evar (H6 :Morphism_N (Psi'' epsilon Kl a)).
apply (N_rewrite (Psi'' epsilon Kl a) H6) in H5.
unfold Psi'' in H5.
rewrite H5.
assumption.
Grab Existential Variables.
admit.
Qed.

Lemma MereoT28 : ~forall A a, A ε Kl a.
Proof.
intro H.
specialize H with (A:=empty)(a:=empty).
apply OntoT5 in H.
assert (H':=H).
apply OntoT9 in H'.
contradiction. 
Qed.

(* The class generated by the empty name does not exist *)
Lemma MereoT29 : forall A, ~(A ε Kl empty).
Proof.
intro A.
red.
intro H.
apply MereoT2 in H. 
apply D1 in H.
apply OntoT17 in H.
assumption.
Qed.

(* identical classes do not yield identical plurals a and b *)
Theorem MereoT30 : forall a b, (exists F, F ε a) /\ (exists G, G ε b) /\ weak_equality (el (Kl a)) (el (Kl b)) ->
      forall B, B ε Kl a -> B ε Kl b.
Proof.
intros a b H1 B H4.
destruct H1 as [H1 H2].
destruct H2 as [H2 H3].
apply MD2.
elim H2; intros E H5. 
assert (G1:=H3).
apply D6 with (a:=el (Kl a))(b:=el (Kl b))(A:=E) in H3.
assert (H6:=H5).
apply MereoT13 in H5. 
split. assert (H10:=H4); apply OntoT5 in H10; assumption.
split. apply H2.
split. 
apply MereoT3 with (A:=Kl b)(B:=E)(a:=b) in H5. 
Focus 2. assumption. 
apply H3 in H5.
assert (H8:=H4).
apply MereoT24 in H4. 
apply OntoT27 in H4.
assert (H9: E ε el (Kl a) /\ singular_equality (Kl a) B).
split; assumption.
apply MereoT16 with (A:=E)(B:=Kl a)(C:=B)(Phi:=el) in H9.
assert (H0: E ε b -> E ε el B).
intro; assumption.
generalize E H0.
firstorder. (* does anything that Prolog does *)
intros G H8.
elim H1; intros J H0. 
apply MereoT13 in H0.
apply MereoT24 in H4.
assert (H9: G ε el B /\ singular_equality B (Kl a)).
split; assumption.
apply MereoT18 in H9.
apply D6 with (a:=el (Kl a))(b:=el (Kl b))(A:=G) in G1.
apply G1 in H9.
assert (H10: Kl b ε Kl b -> G ε el (Kl b)).
intro; assumption.
apply MereoT4 with (A:=Kl b)(B:=G)(a:=b) in H10; assumption.
Qed.

(* =========================== Partial Order ============================== *) 

Parameter PO                 : relation N.
Parameter PPO                : relation N.
Parameter MD11               : forall A a, PO A a ≡≡  (A ε el a).
Parameter MD12               : forall A a, PPO A a ≡≡ (A ε pt a).

Lemma Reflexive_Element_of : Reflexive PO. (* reflexivity Th21 *)
Proof.
red.
intros A H1. 
apply (MereoT6 A A) in H1.
apply MD11.
assumption.
Qed.

Lemma AntiSymmetric_Element_of : Antisymmetric PO.
Proof.
red.
intros A B H0.
destruct H0 as [H1 H2].
apply MD11 in H1.
apply MD11 in H2.
assert (G1:=H1).
assert (G2:=H2).
apply MereoT9 in G1.
apply MereoT9 in G2.
apply (MD1 A B) in H1.
apply (MD1 B A) in H2. 
decompose [and] H1.
decompose [and] H2.
elim H0.
trivial.
intro H5.
apply asymmetric_Part in H5.
apply D15 in H5.
decompose [and] H5.
elim H4.
intro H8.
apply OntoT27. 
assumption.
intro H9.
unfold Part_of in H9.
contradiction.
Qed. 

(* Th20 p408 - Theo IV *)
Lemma Transitive_Element_of : Transitive PO.
Proof.
red.
intros A B C H.
apply MD11.
apply MD1.
destruct H as [H2 H3].
apply MD11 in H2.
apply MD11 in H3.
assert (G2:=H2).
assert (G3:=H2).
apply MereoT9 in G2.
apply OntoT5 in G3.
apply MD1 in H2.
destruct H2.
apply MD1 in H3.
destruct H3.
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
apply (transitivity A B C).
split;assumption.
Qed. 

Theorem PO_is_partial_order : POrder PO.
Proof.
constructor.
apply Reflexive_Element_of.
apply AntiSymmetric_Element_of.
apply Transitive_Element_of.
Qed.

Lemma MereoT34 : forall A B C a, A ε Kl a /\ A ε el B /\ C ε a -> C ε el B.
Proof.
intros A B C a H0.
destruct H0 as [H1 H2].
destruct H2 as [H2 H3].
apply MereoT3 with (A:=A)(a:=a)(B:=C) in H1.
apply MD11.
apply (Transitive_Element_of C A B).
split;apply MD11;assumption.
exact H3.
Qed.

(* ================== EXAMPLE ======================= *)

Variables A1 A2 A3 A4 A5 A6 A7 a1 a2 a3 a4 a5 a6 a7 A a P S E :N.

(* singulars *)

Hypotheses (A_is_A   :  A ε A)
           (A1_is_A1 :  A1 ε A1)
           (A2_is_A2 :  A2 ε A2)
           (A3_is_A3 :  A3 ε A3)
           (A4_is_A4 :  A4 ε A4)
           (A5_is_A5 :  A5 ε A5)
           (A6_is_A6 :  A6 ε A6)
           (A7_is_A7 :  A7 ε A7)
           (E_is_E   :  E ε E)
           (P_is_P   :  P ε P)
           (S_is_S   :  S ε S)
           (A1_is_a :  A1 ε a)
           (A2_is_a :  A2 ε a)
           (A3_is_a :  A3 ε a)
           (A4_is_a :  A4 ε a)
           (A5_is_a :  A5 ε a)
           (A6_is_a :  A6 ε a)
           (A7_is_a :  A7 ε a)

(* basic knowledge *)
           (A1_is_Kla1 :  A1 ε Kl a1)
           (A2_is_Kla2 :  A2 ε Kl a2)
           (A3_is_Kla3 :  A3 ε Kl a3)
           (A4_is_Kla4 :  A4 ε Kl a4)
           (A5_is_Kla5 :  A5 ε Kl a5)
           (A6_is_Kla6 :  A6 ε Kl a6)
           (A7_is_Kla7 :  A7 ε Kl a7)
           (P_is_A3    :  P ε A3) 
           (E_is_union :  E ε union a1 a7)

(****************   el ****************)

           (Ael1 :  A1 ε el A)
           (Ael2 :  A2 ε el A)
           (Ael3 :  A3 ε el A)
           (Ael4 :  A4 ε el A)
           (Ael5 :  A5 ε el A)
           (Ael6 :  A6 ε el A)
           (Ael7 :  A7 ε el A)
           (Ael8 :  P  ε el A3)
           (Akl1 :  A ε Kl a).

Create HintDb Torus.

Hint Resolve A1_is_A1 A2_is_A2 A3_is_A3 A4_is_A4 A5_is_A5 A6_is_A6 A7_is_A7 P_is_P S_is_S E_is_E
        A1_is_Kla1 A2_is_Kla2 A3_is_Kla3 A4_is_Kla4 A5_is_Kla5 A6_is_Kla6 A7_is_Kla7 
        A1_is_a A2_is_a A3_is_a A4_is_a A5_is_a A6_is_a A7_is_a P_is_A3 
        Ael1 Ael2 Ael3 Ael4 Ael5 Ael6 Ael7 Ael8 Akl1 E_is_union A_is_A 
        D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D13 D14 D15 D16 MD1 MD2 MD3 MD4 MD5 MD6 MD7 MD8 MD9 MD10
        MereoT1 MereoT2 MereoT3 MereoT4 MereoT5 MereoT6 MereoT7 MereoT8 MereoT9 MereoT10
        MereoT11 MereoT12 MereoT13 MereoT15 MereoT16 MereoT17 MereoT18 MereoT19 MereoT22
        MereoT23 MereoT24 MereoT25 MereoT26 MereoT27 MereoT28 MereoT29 MereoT30 
        Reflexive_Element_of AntiSymmetric_Element_of Transitive_Element_of 
        asymmetric_Part transitive_Part klass_uniqueness klass_existence : Torus.

Lemma AelTrans : P ε el A3 /\ A3 ε el A -> P ε el A. 
Proof.
intro H.
destruct H as [H1 H2].
apply MD11 in H1.
apply MD11 in H2.
apply MD11.
apply (Transitive_Element_of P A3 A).
split;assumption.
Qed.

(****************   Klass proof  ****************)

Lemma Akl2 :  A ε el (Kl a).
Proof.
apply (MereoT18 A A (Kl a)).
eauto with Torus.
Qed.

Lemma Akl3 : P ε el (Kl a).
Proof.
apply OntoT7 with (B:=A3).
eauto with Torus.
Qed. 

Lemma U_A1_A7 : E ε el (Kl a).
Proof.
apply (MereoT34 A1 (Kl a) E a1).
repeat try (split; eauto with Torus).
Qed. 

End Mereology.






