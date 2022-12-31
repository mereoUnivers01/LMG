From Hammer Require Import Hammer.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Unicode.Utf8.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Setoid Morphisms.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FinFun.

From Hammer Require Reconstr.
Set Hammer ReconstrLimit 25.

Hammer_version.
Hammer_objects.
Set Hammer ATPLimit 180.

Module Type DST_signature.

Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
  (at level 200, right associativity) : type_scope.

Parameter object : Type.

Definition eqobject := @Logic.eq object.

Lemma eqobject_dec : forall x y:object, {eqobject x y} + {~(eqobject x y)}.
Proof.
intros x y;unfold eqobject.
apply excluded_middle_informative.
Qed.

Inductive N : Type := 
    | Caract  : (object -> Prop) -> N.

Definition caract (s :N)(a:object) : Prop := let (f) := s in f a.
Definition In (s :N)(a:object) : Prop := caract s a = True.
Definition incl (s1 s2 :N) := forall a:object, In s1 a -> In s2 a.
Definition set_eq (s1 s2 :N) := forall a:object, In s1 a = In s2 a.

Lemma set_eq_dec : forall x y, {set_eq x y} + {~(set_eq x y)}.
Proof.
intros x y;unfold set_eq;apply excluded_middle_informative.
Qed.

(** DO7 **)
Definition V := Caract (fun s:object => True).
(** DO8 **)
Definition Λ := Caract (fun s:object => False).

Definition ι (a:object) :=
  Caract
    (fun a':object =>
       match eqobject_dec a a' with
       | left h => True
       | right h => False
       end).

Lemma univ : forall A:object, In V A.
Proof.
sauto.
Qed.

(** DN1  **)

Lemma DN1 : forall σ :N, incl σ V.
Proof.
sauto.
Qed.

Lemma  not_True  : (~ True) = False.
Proof.
hauto use: propositional_extensionality.
Qed.

Lemma  not_False  : (~ False) = True.
Proof.
hauto use: propositional_extensionality.
Qed.

Lemma and_true : forall Q:Prop, Q /\ True <-> Q.
Proof.
sauto.
Qed.

Lemma PPNN : forall P:Prop, P -> ~~P.
Proof.
sauto.
Qed.

Lemma notnot : forall P:Prop, P <-> ~~P.
Proof.
intro P;tauto.
Qed.


Theorem contra : forall (p r:Prop), (p -> r)->(~r -> ~p).
Proof.
sauto.
Qed.


Lemma imp_trans : forall P Q R:Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
sauto.
Qed.

Theorem and_commut : ∀ P Q : Prop,  P ∧ Q -> Q ∧ P.
Proof.
sauto.
Qed.

Lemma contra1 : forall p r:Prop, (~p -> ~r) -> (r -> p).
Proof.
intros;rewrite notnot;tauto.
Qed.

Lemma Contra : forall s t:Prop, (s -> t) <-> (~t -> ~s).
Proof.
intros P Q;split;[ apply contra | apply contra1 ].
Qed.

Theorem dual_impl : forall p q : Prop, (p <-> q) <-> ((~p \/ q) /\ (p \/ ~q)).
Proof.
intros;split.
- intro;destruct H;apply imply_to_or in H;split.
  -- assumption.
  -- apply imply_to_or in H0;sfirstorder.
- intro;destruct H as [H1 H2];split.
  -- apply or_to_imply;assumption.
  -- apply contra1;apply or_to_imply;rewrite <-notnot;assumption.
Qed.

Lemma in_propa : forall (x y:N)(A:object), In x A /\ incl x y -> In y A.
Proof.
sauto.
Qed.

Lemma incl_equiv : forall (x y z:N), incl x y /\ set_eq y z -> incl x z.
Proof.
hauto unfold: incl, set_eq.
Qed.

Lemma incl_equivl : forall (x y z:N), incl x y /\ set_eq x z -> incl z y.
Proof.
sfirstorder use: incl_equiv unfold: incl, set_eq.
Qed.

Lemma set_eq_refl : forall x :N, set_eq x x.
Proof.
sauto.
Qed.

Lemma set_eq_sym : forall x y:N, set_eq x y -> set_eq y x.
Proof.
sfirstorder.
Qed.

Lemma set_eq_trans : forall x y z:N, set_eq x y -> set_eq y z -> set_eq x z.
Proof.
scongruence unfold: set_eq.
Qed.

Add Parametric Relation: (N) (set_eq)
reflexivity proved by (set_eq_refl)
symmetry proved by (set_eq_sym)
transitivity proved by (set_eq_trans)
as eq_object_rel.


Lemma incl_set_eq : forall s1 s2:N, set_eq s1 s2 -> incl s1 s2 /\ incl s2 s1.
Proof.
sfirstorder use: incl_equiv, incl_equivl unfold: incl.
Qed.

Lemma set_eq_incl : forall s1 s2:N, incl s1 s2 /\ incl s2 s1 -> set_eq s1 s2.
Proof.
hauto use: propositional_extensionality unfold: set_eq, incl.
Qed.


Lemma set_eq_equiv : forall s s':N, (incl s s' /\ incl s' s) <-> set_eq s s'.
Proof.
sauto use: set_eq_incl, incl_set_eq.
Qed.

Lemma incl_refl : forall s:N, incl s s.
Proof.
scongruence use: set_eq_refl, set_eq_equiv.
Qed.

Lemma incl_intro : forall (sigma to :N), (forall A :object, In sigma A -> In to A) -> incl sigma to.
Proof.
sauto.
Qed.

Lemma set_incl_trans : forall x y z:N, incl x y -> incl y z -> incl x z.
Proof.
hauto unfold: incl.
Qed.

Lemma not_not_iff : forall (P Q : Prop),  ((~P) <-> (~Q)) <-> (P <-> Q).
Proof.
intros P Q;split.
- intro H;destruct H as [H1 H2];split.
  -- intro H';apply imply_to_or in H1;apply imply_to_or in H2;rewrite <-notnot in *. 
     destruct H2;[ assumption | contradiction ].
  -- intro H';apply imply_to_or in H1;apply imply_to_or in H2;rewrite <-notnot in *. 
     destruct H1;[ assumption | contradiction ].
- sauto.
Qed.

Lemma in_singleton : forall A, In (ι A) A.
Proof.
hauto lq: on unfold: In, caract, ι.
Qed.

Lemma refl_singleton : forall A, In (ι A) A <-> True.
Proof.
sauto use: in_singleton.
Qed.

Lemma out_singleton : forall A B, ~(A = B) <-> ~In (ι A) B.
Proof.
intros;split;[ sauto | scongruence use: in_singleton, refl_singleton ].
Qed.

Lemma true_singleton : forall (A B:object), In (ι A) B -> B = A.
Proof.
intros A B H;unfold In in H;cut (~(A = B) <-> ~In (ι A) B).
- hauto unfold: In.
- split;[ intro H';intro H1;apply H';sfirstorder use: out_singleton | sfirstorder ].
Qed.

Lemma rev_singleton : forall (A B:object), B = A -> In (ι A) B.
Proof.
scongruence use: in_singleton.
Qed.

Lemma equiv_singleton : forall (A B:object), In (ι A) B <-> A = B. (**** DN4 ***)
Proof.
sfirstorder use: true_singleton, rev_singleton.
Qed.

Lemma eq_singletons : forall A B:object, incl (ι A)(ι B) -> A = B.
Proof.
hauto use: equiv_singleton, in_singleton unfold: incl.
Qed.

Lemma eq_rev_singletons : forall A B:object, A = B -> incl (ι A)(ι B).
Proof.
scongruence use: incl_refl unfold: incl.
Qed.

Lemma equiv_eq_singletons : forall A B:object, incl (ι A)(ι B) <-> A = B.
Proof.
sauto use: eq_singletons, eq_rev_singletons unfold: ι.
Qed.

Lemma incl_singleton : forall (s:N) (A:object), In s A -> incl (ι A) s.
Proof.
hauto use: in_singleton, rev_singleton, out_singleton, equiv_singleton, refl_singleton unfold: incl.
Qed.

Lemma singleton_incl : forall (s:N)(A:object), incl (ι A) s -> In s A.
Proof.
sauto use: in_singleton unfold: ι, incl.
Qed.

Lemma In_singleton_incl_equiv : forall (s:N)(A:object), incl (ι A) s <-> In s A.
Proof.
sauto use: singleton_incl, incl_singleton.
Qed.

Lemma seq_ind_equality : forall (a x :object), a = x -> set_eq (ι a) (ι x) .
Proof.
scongruence use: in_singleton, set_eq_refl, rev_singleton, out_singleton, equiv_singleton, refl_singleton unfold: set_eq.
Qed.

Lemma ind_seq_equality : forall (a x :object), set_eq (ι a) (ι x) -> a = x.
Proof.
hfcrush use: in_singleton, equiv_singleton, incl_set_eq unfold: incl, set_eq.
Qed.

Lemma ind_seq_equiv : forall a x, set_eq (ι a)(ι x) <-> a = x.
Proof.
sauto use: ind_seq_equality, seq_ind_equality.
Qed.

Lemma singleton_impl_in : forall (A:object)(Σ : N), set_eq (ι A) Σ -> In Σ A.
Proof.
hauto use: in_singleton, set_eq_equiv unfold: set_eq.
Qed.

Lemma incl_in_singleton : forall (Σ Φ :N)(A:object), set_eq (ι A) Φ /\ incl Φ Σ -> In Σ A.
Proof.
sfirstorder use: in_singleton, equiv_singleton, In_singleton_incl_equiv, singleton_impl_in, set_eq_equiv unfold: incl, set_eq.
Qed.

Lemma in_same_set : forall (Σ Φ :N)(A:object), In Σ A /\ set_eq Φ Σ -> In Φ A. 
Proof.
hauto unfold: set_eq.
Qed.

Lemma in_in_singleton : forall (Σ Φ :N)(A:object), set_eq (ι A) Φ /\ In Σ A -> incl Φ Σ.
Proof.
hfcrush use: in_singleton, rev_singleton, out_singleton, set_eq_equiv, In_singleton_incl_equiv, equiv_singleton, refl_singleton unfold: incl, set_eq.
Qed.

Lemma incl_singleton_set : forall (Σ : N)(A B :object), set_eq (ι A) Σ /\ incl (ι B) Σ -> A = B.
Proof.
qauto use: equiv_singleton, In_singleton_incl_equiv unfold: set_eq.
Qed.

Lemma in_singleton_eq : forall (Σ : N)(A B :object), set_eq (ι A) Σ /\ In Σ B -> A = B.
Proof.
hfcrush use: in_singleton, In_singleton_incl_equiv, equiv_singleton, set_eq_equiv unfold: set_eq.
Qed.

Lemma indiv_singl_l : forall (Σ :N)(A :object), set_eq (ι A) Σ -> In Σ A /\ (forall C :object, In Σ C -> C = A).
Proof.
hauto lq: on use: in_singleton, In_singleton_incl_equiv, equiv_singleton, set_eq_equiv unfold: set_eq.
Qed.

Lemma indiv_singl_r : forall (Σ :N)(A :object), In Σ A /\ (forall C:object, In Σ C -> C = A) -> set_eq (ι A) Σ.
Proof.
qauto use: set_eq_incl, incl_singleton, in_singleton unfold: incl.
Qed.

Lemma indiv_singl_equiv : forall (Σ :N)(A :object), In Σ A /\ (forall C:object, In Σ C -> C = A) <-> set_eq (ι A) Σ.
Proof.
sfirstorder use: in_singleton_eq, indiv_singl_r, set_eq_trans, set_eq_sym, singleton_impl_in.
Qed.


(** DN2  **)


Definition Individual (Σ:N) := exists A:object, set_eq (ι A) Σ.

(**  DN3   **)

Definition eta (Σ σ :N) := Individual Σ /\ incl Σ σ.

(************* DN8 ****************)

(** Ontology modelling **)


Definition neg (P :N) : N :=
    Caract (fun A:object => IF_then_else (Individual (ι A) /\ ~(eta (ι A) P)) True False).

Definition n_disjunction (Φ Σ:N) : N :=  Caract (fun P:object => IF_then_else (eta (ι P) Φ \/ eta (ι P) Σ) True False).

Notation "a '∪' b" := (n_disjunction a b)  (at level 50).

Definition n_conjunction (a b :N) : N := 
                          Caract (fun A:object => IF_then_else (eta (ι A) a /\ eta (ι A) b) True False).

Notation "a '∩' b" := (n_conjunction a b)  (at level 50).

Definition singular_eq (A B:N) := eta A B /\ eta B A.
Notation "a '≡' b" := (singular_eq a b)  (at level 80).

Definition weak_eq (a b :N) := forall A, eta A a <-> eta A b.
Notation "a '≈' b" := (weak_eq a b)  (at level 80).

Definition exists_at_least (a :N) : Prop := exists A, eta A a.
Notation "'!' b" := (exists_at_least b)  (at level 80).

Definition exists_at_most (a :N) : Prop := forall B C, eta B a /\ eta C a -> B ≡ C.

Definition exists_exactly (A :N) : Prop := forall b, eta A b.

Definition diff_ind (A B:N) : Prop := Individual A /\ Individual B /\ ~singular_eq A B.
Notation "A '≢' B" := (diff_ind A B)  (at level 80).

(** DO4 **)

Definition weakInclusion (a b :N) := forall A, eta A a -> eta A b.
Notation "a '⊆' b" := (weakInclusion a b)  (at level 60).

(* partial inclusion : some *)

Definition partialInclusion (a b :N) := exists A, (eta A a /\ eta A b).
Notation "a 'Δ' b" := (partialInclusion a b)  (at level 40).

Lemma DO5 : forall (a b :N), a ≈ b <-> a ⊆ b /\ b ⊆ a.
Proof.
strivial unfold: weakInclusion, weak_eq.
Qed.

Lemma weak_eq_equiv : forall a b, (forall A, eta A a <-> eta A b) <-> (a ⊆ b /\ b ⊆ a).
Proof.
sauto.
Qed.

Lemma weak_eq_refl : forall x, x ≈ x.
Proof.
sauto.
Qed.

Lemma weak_eq_sym : forall x y, x ≈ y -> y ≈ x.
Proof.
strivial unfold: weak_eq.
Qed.

Lemma weak_eq_trans : forall x y z, x ≈ y -> y ≈ z -> x ≈ z.
Proof.
hfcrush unfold: weak_eq.
Qed.

Add Parametric Relation: (N)(weak_eq)
reflexivity proved by (weak_eq_refl)
symmetry proved by (weak_eq_sym)
transitivity proved by (weak_eq_trans)
as eq_N_rel.

Definition Psi_plur (E1:N -> Prop)(E2:N) := E1 E2.

Add Parametric Morphism (A : N) : (Psi_plur (eta A)) with signature (weak_eq) ==> (iff) as extens_plur.
Proof.
sauto unfold: weak_eq, Psi_plur.
Qed.

Add Parametric Morphism (A:object): (eta (ι A)) with signature (set_eq) ==> (iff) as ext_singl.
Proof.
hauto lq: on use: incl_equiv, set_eq_sym unfold: eta.
Qed.

Lemma singular_eq_sym : forall A B, A ≡ B -> B ≡ A.
Proof.
sfirstorder.
Qed.

Lemma singular_eq_trans : forall A B C, A ≡ B /\ B ≡ C -> A ≡ C.
Proof.
intros A B C [H1 H2];unfold singular_eq in *;destruct H1, H2;sfirstorder use: set_incl_trans unfold: eta.
Qed.

Lemma In_indiv : forall (B:object)(Φ :N), Individual Φ /\ In Φ B -> set_eq Φ (ι B).
Proof.
sfirstorder use: in_singleton_eq unfold: set_eq, Individual.
Qed.

Lemma indiv_singleton : forall A :object, Individual (ι A) = True.
Proof.
sauto use: propositional_extensionality, PropExtensionalityFacts.PropExt_imp_ProvPropExt, seq_ind_equality unfold: Individual.
Qed.

Lemma eta_singular : forall Φ :N, eta Φ Φ -> exists A:object, set_eq (ι A) Φ.
Proof.
sauto.
Qed.

Lemma singular_eta : forall Φ :N, (exists A:object, set_eq (ι A) Φ) -> eta Φ Φ.
Proof.
sauto use: incl_refl unfold: Individual, eta.
Qed.

Lemma eta_singular_equiv : forall Φ :N, eta Φ Φ <-> exists A:object, set_eq (ι A) Φ.
Proof.
sauto use: singular_eta, eta_singular.
Qed.

Lemma Ind_impl_in : forall (Σ:N), Individual Σ -> exists A, In Σ A.
Proof.
strivial use: eta_singular_equiv, singleton_impl_in, eta_singular unfold: eta, Individual, incl.
Qed.

Lemma singl_in_eta : forall (A :object)(Φ : N), eta (ι A) Φ -> In Φ A.
Proof.
strivial use: singleton_incl unfold: eta.
Qed.

Lemma eta_in_singl : forall (A :object)(Φ : N),  In Φ A -> eta (ι A) Φ.
Proof.
strivial use: indiv_singleton, incl_singleton unfold: eta.
Qed.

Lemma eta_singl_in : forall (A :object)(Φ : N), eta (ι A) Φ <-> In Φ A.
Proof.
sauto use: eta_in_singl, singl_in_eta.
Qed.

Lemma indiv_singletonl : forall (Σ :N)(A :object), Individual Σ /\ In Σ A -> set_eq (ι A) Σ.
Proof.
sfirstorder use: ind_seq_equiv, indiv_singl_equiv, seq_ind_equality, in_singleton, equiv_singleton, Ind_impl_in unfold: Individual, set_eq.
Qed.

Lemma rewr_singleton_in_eta : forall (σ ϕ:N)(A :object), eta σ ϕ /\ set_eq σ (ι A) -> eta (ι A) ϕ.
Proof.
hauto use: incl_equivl, indiv_singleton unfold: eta.
Qed.

Lemma rewl_singleton_in_eta : forall (σ ϕ:N)(A :object), eta (ι A) ϕ /\ set_eq σ (ι A) -> eta σ ϕ.
Proof.
qauto use: set_eq_sym, in_in_singleton, eta_singl_in unfold: Individual, ι, eta.
Qed.

Lemma eta_singleton_l : forall (σ :N)(A :object), set_eq (ι A) σ -> eta (ι A) σ.
Proof.
sauto use: eta_in_singl, singleton_impl_in.
Qed.

Lemma weak_to_incl : forall a b, a ⊆ b <-> incl a b.
Proof.
hauto use: eta_singl_in, incl_in_singleton, set_eq_refl, set_incl_trans unfold: weakInclusion, incl, eta.
Qed.

Theorem weak_eq_to_set_eq : forall a b, a ≈ b <-> set_eq a b.
Proof.
hfcrush use: incl_set_eq, set_eq_equiv, DO5, weak_to_incl.
Qed.


Lemma singular_singleton : forall P Q, P ≡ Q -> Individual P /\ Individual Q.
Proof.
sauto.
Qed.

Lemma singular_eq_eq_obj : forall A B, A ≡ B -> set_eq A B.
Proof.
strivial use: set_eq_equiv unfold: eta, singular_eq.
Qed.

Lemma eq_obj_singular_eq : forall A B, (Individual A /\ Individual B) -> (set_eq A B -> A ≡ B).
Proof.
strivial use: set_eq_equiv, set_eq_sym unfold: singular_eq, eta.
Qed.

Theorem singular_eq_dec : forall A B, (Individual A /\ Individual B) -> (set_eq A B <-> A ≡ B).
Proof.
sauto use: singular_eq_eq_obj, eq_obj_singular_eq.
Qed.

Lemma singular_eq_singl : forall A B:object, (ι A) ≡ (ι B) <-> A = B.
Proof.
hauto use: indiv_singleton, seq_ind_equality, singular_eq_dec, ind_seq_equality, eq_obj_singular_eq.
Qed.


(** syntax for theorems and lemmas:
 - Nxx    -> Clay's syntax
 - Ontoxx -> syntax from Lesniewski's ontology
 - Miexx  -> Mieville's syntax
 - Lejxx  -> Lejewski's syntax
 - Sinxx  -> Sinsi's syntax
**)

Declare Scope mereo_scope.

Parameter le_object : object -> object -> Prop.

Notation "A '≤' B" := (le_object A B)  (at level 70) : mereo_scope.

Open Scope mereo_scope.

(***** initial axiom ***)

Axiom two_elem : (exists A B:object, ~(A = B)).

(** Mereological Definitions **)

Definition el (Φ :N) : N :=
    Caract (fun A:object => IF_then_else (Individual Φ /\ exists (B C :object), In (ι A) B /\ In Φ C /\ B ≤ C) True False).

Definition pt (Φ :N) : N :=
    Caract (fun A:object => IF_then_else (Individual (ι A) /\ eta (ι A)(el Φ) /\ ~(set_eq Φ (ι A))) True False).

Definition klass (a :N) : N := Caract (fun P:object =>  IF_then_else (Individual (ι P) /\ (forall B, eta B a -> eta B (el (ι P))) /\
                                              (forall B, eta B (el (ι P)) -> exists C D, eta C a /\ eta D (el C) /\ eta D (el B))) True False).

Definition coll (a :N) : N := Caract (fun P:object => IF_then_else (Individual (ι P) /\ forall Q, eta Q (el (ι P)) ->
                                                      exists C D, eta C a /\ eta D (el C) /\ eta D (el Q) /\ eta C (el (ι P))) True False).


Definition SubColl (Q :N) : N := Caract (fun P:object => IF_then_else (Individual (ι P) /\ forall C, eta C (el (ι P)) -> eta C (el Q)) True False).

Definition ext (Q :N) : N := 
           Caract (fun P:object => IF_then_else (Individual (ι P) /\ Individual Q /\ ~(exists C, eta C (el Q) /\ eta C (el (ι P)))) True False).

Definition ov (Q :N) : N := Caract (fun P:object =>  IF_then_else (Individual (ι P) /\ Individual Q /\ exists C, eta C (el Q) /\ eta C (el(ι P))) True False).

Definition relCompl (Q R:N) : N := Caract (fun P:object => IF_then_else (Individual (ι P) /\ 
                                                           eta Q (SubColl R) /\ eta (ι P)(klass ((el R) ∩ (ext Q)))) True False).

Definition sum (a :N) : N := Caract (fun P:object => IF_then_else (eta (ι P)(klass a) /\ forall Q R, eta Q a /\ eta R a -> eta Q R \/ eta Q (ext R)) True False).




(** derived from axiom P **)

Axiom BD : forall A B, A ≤ B <-> (In V A /\ In V B /\ (B ≤ B -> (forall β α, incl α V /\ incl β V /\ In α B /\
                               (forall C, In β C <-> ((forall D, In α D -> D ≤ C) /\ (forall D, D ≤ C ->
                               exists E F, In α E /\ F ≤ D /\ F ≤ E))) -> exists L, set_eq β (ι L) /\ A ≤ L))).

Lemma BD': forall A B, A ≤ B <-> (B ≤ B -> (forall β α, incl α V /\ incl β V /\ In α B /\ (forall C, In β C <->
                               ((forall D, In α D -> D ≤ C) /\ (forall D, D ≤ C -> exists E F, 
                               In α E /\ F ≤ D /\ F ≤ E))) -> (exists L, set_eq β (ι L) /\ A ≤ L))).
Proof.
hfcrush use: BD, univ.
Qed.

Lemma le_object_refl : reflexive object le_object.
Proof.
red;intro A;rewrite BD';intro H;assert (H0:=H);rewrite BD' in H0;apply H0;assumption.
Qed.

Definition sup (a :N) : N := Caract (fun A:object => IF_then_else ((forall D, In a D -> D ≤ A) /\ forall D:object, 
                          D ≤ A -> exists E F, In a E /\ F ≤ D /\ F ≤ E) True False).

Lemma DBD1 : forall A a, In (sup a) A <-> ((forall D, In a D -> D ≤ A) /\ forall D:object, D ≤ A -> 
                                          exists E F, In a E /\ F ≤ D /\ F ≤ E).
Proof.
intros A a;split.
- intro H;unfold sup in H;unfold In in H;unfold IF_then_else in H;simpl in H;assert (H':True).
  -- auto.
  -- rewrite <-H in H';clear H;destruct H'.
     --- destruct H as [[H1 H2] H];split;(unfold In;assumption).
     --- destruct H;contradiction.
- intro H;destruct H as [H1 H2];unfold sup;unfold In;unfold IF_then_else;simpl;apply propositional_extensionality;split;
  [ intro;auto | intro H3;classical_left;split;[ split;sauto | auto ]].
Qed.

Lemma BD2 : forall A a, In a A -> exists L, set_eq (sup a)(ι L).
Proof.
intros A a H1;assert (H2:A ≤ A).
- apply le_object_refl.
- assert (H0:=H2);rewrite BD in H2. apply H2 with (β:=sup a)(α:=a) in H0.
  -- destruct H0 as [L [H0 H3]];exists L;assumption.
  -- split;[ apply DN1 |
     split;[ apply DN1 |
     split;[ assumption |
     intro B;split;[ strivial use: DBD1 | sfirstorder use: DBD1 ]]]].
Qed.

Lemma BD3 : forall A, In (sup (ι A)) A.
Proof.
intro A;rewrite DBD1;split.
- intros D H;rewrite equiv_singleton in H;rewrite H;apply le_object_refl.
- intros D H;exists A, D;split;[ apply in_singleton | split;[ apply le_object_refl | assumption ]].
Qed.

Lemma BD4 : forall A C, (forall G, C ≤ G) -> In (sup (ι C)) A.
Proof.
intros A C H;rewrite DBD1;split.
- intros B H';rewrite equiv_singleton in H';rewrite <-H';apply H.
- intros B H';exists C, C;split;[ apply in_singleton | split;apply H ].
Qed.

Lemma BD5 : forall A B C:object, (forall G, C ≤ G) -> A = B.
Proof.
intros A B C H;assert (H1:In (sup (ι C)) A).
- apply BD4 with (A:=A) in H;assumption.
- apply BD4 with (A:=B) in H;assert (H2:exists L, set_eq (sup (ι C))(ι L)).
  -- apply BD2 with (A:=C);apply in_singleton.
  -- destruct H2 as [L H2];assert (In (ι L) A).
     --- apply in_same_set with (Σ:=(sup (ι C)));split;[ assumption | apply set_eq_sym;assumption ].
     --- assert (In (ι L) B).
         ---- apply in_same_set with (Σ:=(sup (ι C)));split;[ assumption | apply set_eq_sym;assumption ].
         ---- rewrite equiv_singleton in H0;rewrite equiv_singleton in H3;rewrite H0 in H3;assumption.
Qed.

Lemma BD6 : forall A B D:object, ~(A = B) -> (exists C, ~(D ≤ C)).
Proof.
intros A B D. assert (H1:(∃ C : object, ¬ D ≤ C) <-> ~~(∃ C : object, ¬ D ≤ C)).
- apply notnot.
- rewrite H1;apply contra;clear H1;intro H1;apply BD5 with (C:=D);intro G;apply not_ex_not_all with (n:=G) in H1;assumption.
Qed.

(** proof of ZD **)

Lemma BD7 : (exists A B:object, ~(A = B)) -> (forall C, exists D, ~(C ≤ D)).
Proof. 
intro H;destruct H as [A [B H1]];intro D;apply BD6 with (D:=D) in H1;destruct H1 as [C H1];exists C;assumption.
Qed.

Lemma BD8 : (exists A B:object, ~(A = B)) -> forall B:object, (forall β α, (In α B /\ (forall C, In β C <->
                                ((forall D, In α D -> D ≤ C) /\ (forall D, D ≤ C -> exists E F, In α E /\ F ≤ D /\ F ≤ E)))) ->
                                (In α B /\ (forall C, In β C <-> ((forall D, In α D -> D ≤ C) /\
                                (forall D H, D ≤ C /\ ~(D ≤ H) -> exists E F G, In α E /\ F ≤ D /\ F ≤ E /\ ~(F ≤ G)))))).
Proof.
intros H1 B b a H2;destruct H2 as [H2 H3];split.
- assumption.
- intro C;rewrite H3;split.
  -- intro H6;destruct H6 as [H6 H7];split.
     --- assumption.
     --- intros D H H8;clear H3;destruct H8 as [H8 H9];apply H7 in H8;destruct H8 as [E [F [H8 [H10 H11]]]];
         apply BD7 with (C:=F) in H1;destruct H1 as [G H1];sauto.
  -- intro H4;destruct H4 as [H4 H5];clear H3;split.
     --- assumption.
     --- intros D H3;apply BD7 with (C:=D) in H1;destruct H1 as [H H1];assert (∃ E F G : object, In a E ∧ F ≤ D ∧ F ≤ E ∧ ¬ F ≤ G);sauto.
Qed.

Lemma BD8' : (exists A B:object, ~(A = B)) -> forall B:object, (forall β α, (In α B /\ (forall C, In β C <-> ((forall D, In α D -> D ≤ C) /\
                                (forall D H, D ≤ C /\ ~(D ≤ H) -> exists E F G, In α E /\ F ≤ D /\ F ≤ E /\ ~(F ≤ G))))) -> (In α B /\ (forall C, 
                                In β C <-> ((forall D, In α D -> D ≤ C) /\ (forall D, D ≤ C -> exists E F, In α E /\ F ≤ D /\ F ≤ E))))).
Proof.
intros H1 B b a H2;destruct H2 as [H2 H3];split.
- assumption.
- intro C;rewrite H3;split.
  -- intro H6;destruct H6 as [H6 H7];split.
     --- assumption.
     --- intros D H4;apply BD7 with (C:=D) in H1;destruct H1 as [H H1];hfcrush.
  -- intro H4;destruct H4 as [H4 H5];clear H3;split.
     --- assumption.
     --- intros D H H6;destruct H6;apply H5 in H0;destruct H0 as [E [F [H6 [H7 H8]]]];apply BD7 with (C:=F) in H1;sauto.
Qed.

Lemma BD9 : (exists A B:object, ~(A = B)) -> forall B:object, (forall β α, (In α B /\ (forall C, In β C <-> ((forall D, In α D -> D ≤ C) /\
                                (forall D H, D ≤ C /\ ~(D ≤ H) -> exists E F G, In α E /\ F ≤ D /\ F ≤ E /\ ~(F ≤ G))))) <-> (In α B /\ (forall C, 
                                In β C <-> ((forall D, In α D -> D ≤ C) /\ (forall D, D ≤ C -> exists E F, In α E /\ F ≤ D /\ F ≤ E))))).
Proof.
intros H1 B b a;split;[ intro H2;apply BD8';auto | intro H2;apply BD8;auto ].
Qed.

(**  BD inferentially equivalent to W' **)


Lemma BD_W : (exists A B:object, ~(A = B)) -> (forall A B:object, A ≤ B <-> (B ≤ B -> (forall β α, incl α V /\ incl β V /\In α B /\ (forall C, In β C <-> ((forall D, In α D -> D ≤ C) /\
                                (forall D, D ≤ C -> exists E F, In α E /\ F ≤ D /\ F ≤ E))) -> exists L, set_eq β (ι L) /\ A ≤ L))) <-> 
                                forall A B:object, A ≤ B <-> (B ≤ B -> (forall β α, incl α V /\ incl β V /\ In α B /\ (forall C, In β C <-> ((forall D, In α D -> D ≤ C) /\ 
                                (forall D H, D ≤ C /\ ~(D ≤ H) -> exists E F G, In α E /\ F ≤ D /\ F ≤ E /\ ~(F ≤ G)))) -> exists L, set_eq β (ι L) /\ A ≤ L)).
Proof.
intros H0;split.
- intros H1 A B;specialize (H1 A B);split.
  -- intros H2 H3 b a H4;rewrite H1 in H2;apply H2 with (β:=b)(α:=a).
     --- assumption.
     --- rewrite <-BD9;assumption.
  -- intro H2;rewrite H1;clear H1;intros;apply H2 with (β:=β)(α:=α).
     --- assumption.
     --- rewrite BD9;assumption.
- intro H1;split.
  -- intros H2 H3 b a H4;rewrite H1 in H2;apply H2 with (β:=b)(α:=a).
     --- assumption.
     --- rewrite BD9;assumption.
  -- intro H2;rewrite H1;clear H1;intros;apply H2 with (β:=β)(α:=α).
      --- assumption.
      --- rewrite <-BD9;auto.
Qed.

Lemma W : forall A B:object, A ≤ B <-> (B ≤ B -> (forall β α, incl α V /\ incl β V /\ In α B /\ (forall C, In β C <-> ((forall D, In α D -> D ≤ C) /\ 
                           (forall D H, D ≤ C /\ ~(D ≤ H) -> exists E F G, In α E /\ F ≤ D /\ F ≤ E /\ ~(F ≤ G)))) -> exists L, set_eq β (ι L) /\ A ≤ L)).
Proof.
assert (H1:exists A B:object, ~(A = B));[ apply two_elem | apply BD_W in H1;rewrite <-H1;apply BD' ].
Qed.

Lemma DW1 : forall A a, In (sup a) A <-> ((forall D, In a D -> D ≤ A) /\ forall D H:object, D ≤ A /\
           ~(D ≤ H) -> exists E F G, In a E /\ F ≤ D /\ F ≤ E /\ ~(F ≤ G)).
Proof.
intros A a;assert (H3:exists A B:object, ~(A = B)).
- apply two_elem.
- split.
  -- intro H1;rewrite DBD1 in H1;destruct H1 as [H1 H2];split.
     --- assumption.
     --- intros D H H4;destruct H4 as [H4 H8];apply H2 in H4;destruct H4 as [E [F [H4 [H5 H6]]]];apply BD7 with (C:=F) in H3.
         destruct H3 as [G H3];exists E, F, G;split;[ assumption | split;[ assumption | split;assumption ]].
  -- intro H1;destruct H1 as [H1 H2];rewrite DBD1;split.
     --- assumption.
     --- intros D H4;apply BD7 with (C:=D) in H3. destruct H3 as [H H3];assert (∃ E F G : object, In a E ∧ F ≤ D ∧ F ≤ E ∧ ¬ F ≤ G).
         ---- apply H2 with (H:=H);split;assumption.
         ---- destruct H0 as [E [F [G [H5 [H6 [H7 H8]]]]]];sauto.
Qed.

Lemma W2 : forall A B, (forall K, B ≤ K -> A ≤ K) -> A ≤ B.
Proof.
hauto depth: 2 lq: on exh: on use: univ, BD.
Qed.

Lemma W3 : forall A B a, A ≤ B /\ In a B -> exists L, set_eq (sup a)(ι L) /\ A ≤ L.
Proof.
intros A B a H;destruct H as [H1 H2];apply W with (A:=A)(B:=B)(β:=sup a)(α:=a).
- assumption.
- apply le_object_refl.
- split;[ sauto | split;[ sauto | split;[ assumption | intro;apply DW1 ]]].
Qed.

Lemma W4 : forall A a, In a A -> exists L, set_eq (sup a)(ι L).
Proof.
hfcrush use: le_object_refl, W3. 
Qed.

Definition lowerBound (B:object) : N := Caract (fun A:object => IF_then_else (A ≤ B) True False).

Lemma DW2 : forall A B, In (lowerBound B) A <-> (A ≤ B).
Proof.
intros A B;split.
- intro H;unfold lowerBound in H;unfold In in H;unfold IF_then_else in H;simpl in H;assert (H':True);
  [ auto | rewrite <-H in H';destruct H';sauto ].
- intro H;unfold lowerBound;unfold In;unfold IF_then_else;simpl;apply propositional_extensionality;split;sauto.
Qed.

Lemma W5 : forall A, In (sup (lowerBound A)) A.
Proof.
intro A;rewrite DW1;split.
- intros D H;unfold lowerBound in H;unfold In in H;unfold IF_then_else in H;simpl in H;assert (H':True);
  [ auto | rewrite <-H in H';clear H;destruct H';sauto ].
- intros C D H;destruct H as [H1 H2];exists C, C, D;split.
  -- rewrite DW2;assumption.
  -- split;[ apply le_object_refl | split;[ apply le_object_refl | assumption ]].
Qed.

Lemma W6 : forall A, set_eq (ι A)(sup (lowerBound A)).
Proof.
intro A;assert (H1:In (lowerBound A) A).
- rewrite DW2;apply le_object_refl.
- apply W4 in H1;destruct H1 as [L H1];apply set_eq_sym in H1;assert (H2:In (sup (lowerBound A)) A /\ set_eq (ι L) (sup (lowerBound A))).
  -- split;[ apply W5 | assumption ].
  -- apply in_same_set in H2;rewrite equiv_singleton in H2;rewrite H2 in H1;assumption.
Qed.

(** le: partial orering relation **)

Theorem le_object_transitive : forall A B C, A ≤ B /\ B ≤ C -> A ≤ C.
Proof.
intros A B C H;destruct H as [H1 H2];assert (H3:B ≤ B <-> B ≤ C).
- split;[ intro;assumption | intro;apply le_object_refl ].
- rewrite <-DW2 in H3;assert (H4:A ≤ B /\ In (lowerBound C) B).
  -- strivial use: DW2.
  -- apply W3 in H4;destruct H4 as [L H4];destruct H4 as [H4 H5];assert (H7:set_eq (ι C)(sup (lowerBound C))).
     --- apply W6.
     --- assert (H8:set_eq (ι C)(ι L));[ scongruence use: W5, equiv_singleton unfold: set_eq | hauto use: ind_seq_equality ].
Qed.

Add Parametric Morphism: (sup)    with signature (set_eq) ==> (set_eq)  as sup_morphism.
Proof.
intros x y H;unfold set_eq;intro A;apply propositional_extensionality;repeat rewrite DBD1;split.
- intro;destruct H0;split;[ qauto unfold: set_eq | hauto unfold: set_eq ].
- intro;destruct H0;split;[ hauto unfold: set_eq | qauto unfold: set_eq ].
Qed.


Theorem le_object_antisym : forall A B, A ≤ B /\ B ≤ A -> A = B.
Proof.
intros A B H;destruct H as [H1 H2];assert (H3:forall D, D ≤ A <-> D ≤ B).
- intro D;split;sauto use: le_object_transitive.
- setoid_rewrite <-DW2 in H3;assert (set_eq (lowerBound A)(lowerBound B)).
  -- unfold set_eq;intro C;apply propositional_extensionality;sauto.
  -- rewrite <-ind_seq_equiv;apply sup_morphism in H;scongruence use: W6 unfold: set_eq.
Qed.


(** Elementary Ontology **)

Lemma N1 : forall (Σ :N), eta Σ Σ <-> Individual Σ.
Proof.
strivial use: incl_refl unfold: eta.
Qed.

Lemma N2 : forall (Σ σ :N), eta Σ σ -> eta Σ Σ.
Proof.
sfirstorder use: N1 unfold: eta.
Qed.

Lemma N3 : forall (Σ σ :N)(A:object), (Individual Σ /\ In Σ A /\ In σ A) -> incl Σ σ.
Proof.
hauto lq: on use: indiv_singletonl, in_in_singleton.
Qed.

Lemma N4 : forall (Σ σ Φ :N), eta Σ σ /\ eta Φ Σ -> set_eq Φ Σ.
Proof.
hauto lq: on rew: off use: set_eq_equiv, N1, in_singleton_eq, N2, in_in_singleton, in_propa, eta_singular, 
Ind_impl_in, indiv_singl_equiv unfold: eta.
Qed.

Lemma N5 : forall (Σ σ Φ:N), eta Σ σ /\ eta Φ Σ -> eta Φ σ.
Proof.
sfirstorder use: incl_equivl, set_eq_sym, N4 unfold: eta.
Qed.

Lemma N6 : forall (Σ σ Φ Ψ :N), eta Σ σ /\ eta Φ Σ /\ eta Ψ Σ -> eta Φ Ψ.
Proof.
hauto lq: on use: set_eq, N2, N1, set_eq_equiv, set_eq_sym, set_eq_trans, N4 unfold: eta.
Qed.

Lemma N7 : forall A :object, In (ι A) A.
Proof.
sauto use: in_singleton.
Qed.

Lemma N9 : forall A :object, Individual (ι A).
Proof.
sauto.
Qed.

Lemma N10 : forall (σ :N)(A : object), In σ A -> eta (ι A) σ.
Proof.
sauto use: eta_in_singl.
Qed.

Lemma N11 : forall (σ :N)(A : object), eta (ι A) σ -> In σ A.
Proof.
sauto use: singl_in_eta.
Qed.

Lemma N12 : forall (σ :N)(A : object), In σ A <-> eta (ι A) σ.
Proof.
strivial use: eta_singl_in.
Qed.

Lemma N13 : forall A:object, In (ι A) A <-> eta (ι A) (ι A).
Proof.
strivial use: equiv_singleton, eta_in_singl.
Qed.

Lemma N14 : forall (Σ:N)(A:object), (forall Φ Ψ:N, eta Φ Σ /\ eta Ψ Σ -> eta Φ Ψ) /\ In Σ A -> forall B, In Σ B -> A = B.
Proof.
hauto lq:on use: N12, eq_singletons unfold: eta.
Qed.

Lemma N15 : forall (θ Σ σ :N), eta θ Σ /\ (forall Φ : N, eta Φ Σ -> eta Φ σ) /\
                                              (forall Φ Ψ : N, eta Φ Σ /\ eta Ψ Σ -> eta Φ Ψ) -> eta Σ σ.
Proof.
qauto depth: 4 l: on use: N14, set_eq_sym, eta_singular_equiv, set_eq_incl, N2, eta_singular, in_singleton, 
indiv_singl_l unfold: incl, set_eq, eta.
Qed.

(** epsilon specification **)

Lemma N16 : forall (Σ σ :N), eta Σ σ  <-> ((exists θ:N, eta θ Σ) /\ (forall Φ : N, eta Φ Σ -> eta Φ σ) /\
                                              (forall Φ Ψ : N, eta Φ Σ /\ eta Ψ Σ -> eta Φ Ψ)).
Proof.
intros Sigma sigma;split.
- intro H;split;[ exists Sigma;apply N1;destruct H;assumption | hauto depth: 2 lq: on exh: on use: N5, N6 ].
- hauto use: N15.
Qed.

Lemma N17 : forall (σ τ Σ :N), incl σ τ /\ eta Σ σ -> eta Σ τ.
Proof.
strivial use: set_incl_trans unfold: eta.
Qed.

Lemma N18 : forall (σ τ :N), incl σ τ -> (forall Σ :N, eta Σ σ -> eta Σ τ).
Proof.
sauto use: N17.
Qed.

Lemma N19 : forall (σ τ:N), (forall Σ :N, eta Σ σ -> eta Σ τ) -> (forall A :object, In σ A -> In τ A).
Proof.
sauto use: N10, N11.
Qed.

Lemma N20 : forall (σ τ:N), (forall Σ :N, eta Σ σ -> eta Σ τ) -> incl σ τ.
Proof.
hauto use: incl_intro, N19.
Qed.

Lemma N21 : forall (σ τ:N), incl σ τ <-> (forall Σ :N, eta Σ σ -> eta Σ τ).
Proof.
sauto use: N20, N18.
Qed.

Lemma N22 : forall (σ τ:N), set_eq σ τ <-> (forall Σ :N, eta Σ σ <-> eta Σ τ).
Proof.
hfcrush use: N20, N17, set_eq_equiv.
Qed.

Lemma N27 : forall Σ:N, Individual Σ -> exists A, In Σ A /\ set_eq Σ (ι A) /\ In V A.
Proof.
hauto lq: on use: univ, Ind_impl_in, In_indiv.
Qed.

Lemma N24 : forall Σ :N, Individual Σ <-> exists A :object, In V A /\ set_eq Σ (ι A).
Proof.
strivial use: N27 unfold: set_eq, Individual.
Qed.


(* ========================== some theorems for Distributive classes ================================== *)

Lemma eq_singl : forall x y:object, eta (ι x)(ι y) <-> x = y.
Proof.
strivial use: eq_rev_singletons, eq_singletons, N9 unfold: eta.
Qed.

Ltac solve_functor := split;[ assumption | symmetry;assumption ].

Ltac solve_op_in_goal opt :=
match goal with 
  | [ |- In (opt _) _ ] => unfold In;unfold opt;unfold IF_then_else;simpl;apply propositional_extensionality;split;[ intro;auto | intro;left ]
  | _ => idtac
end.

Ltac solve_op_in_hyp H opt x :=
match type of H with
  | eta ?A (opt ?B) => unfold eta in H;let H20 := fresh in destruct H as [H H20];destruct H as [x H];let H21 := fresh in assert (H21:set_eq (ι x) A /\ incl A (opt B));[
    split;assumption | apply incl_in_singleton in H21;unfold In in H21;unfold opt in H21;unfold IF_then_else in H21;simpl in H21;let H22 := fresh in assert (H22:True);[
      auto | rewrite <-H21 in H22;clear H21 ]]
end.

Ltac solve_op_in_red_hyp H opt :=
match type of H with
  | In (opt ?B) ?x => unfold In in H;unfold opt in H;unfold IF_then_else in H;simpl in H;let H22 := fresh in assert (H22:True);[
      auto | rewrite <-H in H22;clear H ]
end.

Lemma OntoT0 : forall A B C, A ≡ B /\ B ≡ C -> A ≡ C.
Proof.
sfirstorder use: N6 unfold: singular_eq.
Qed.

Lemma OntoT1 : forall A a, eta A a -> (exists B, eta B A).
Proof.
sauto use: N2.
Qed.

Lemma OntoT2 : forall A a C D, eta A a /\ eta C A /\ eta D A -> eta C D.
Proof.
apply N6.
Qed.

Lemma OntoT2' : forall A a, eta A a -> (forall C D, eta C A /\ eta D A -> C ≡ D).
Proof.
hauto depth: 2 lq: on exh: on use: N2, N6 unfold: singular_eq.
Qed.

Lemma Indiv_cv : forall A, Individual A -> (forall C D, eta C A /\ eta D A -> C ≡ D).
Proof.
hauto lq: on use: N1, N6 unfold: singular_eq.
Qed.

Lemma OntoT3 : forall A a, eta A a -> forall C, eta C A -> eta C a.
Proof.
sauto use: N5.
Qed.

Lemma OntoT6 : forall A B a, eta A B /\ eta B a -> eta B A.
Proof.
hfcrush use: N2, N6.
Qed.

Lemma OntoT7 : forall A B a, eta A B /\ eta B a -> eta A a.
Proof.
sfirstorder use: N5.
Qed.

Lemma D6 : forall A, eta A Λ <-> eta A A /\ ~(eta A A).
Proof.
hauto depth: 2 lq: on exh: on use: singleton_impl_in unfold: Λ, Individual, incl, In, eta, caract.
Qed.

Lemma OntoT8 : forall A, ~(eta A Λ).
Proof.
sfirstorder use: D6.
Qed.

Lemma OntoT9 : ~(eta Λ Λ).
Proof.
sauto use: OntoT8.
Qed.

Lemma OntoT14 : forall A a, eta A a -> eta A A.
Proof.
sauto use: N2.
Qed.

Lemma OntoT15 : forall A, (exists a, eta A a) <-> eta A A.
Proof.
strivial use: OntoT14, OntoT1.
Qed.

(** the empty name does not denote a particular **)

Lemma OntoT17 : ~(!Λ).
Proof.
unfold exists_at_least;intro;destruct H as [A H];revert H;apply OntoT8.
Qed.

Lemma OntoT19 : forall A a, eta A a -> exists B, eta A B /\ eta B a.
Proof.
sauto use: N2.
Qed.

Lemma OntoT21 : forall A B a, eta A B /\ eta B a -> A ≡ B.
Proof.
hfcrush use: N1, N2, Indiv_cv.
Qed.

Lemma eq_indiv_in_eta : forall A B a, eta A a /\ set_eq A B -> eta B a.
Proof.
qauto use: set_eq_trans, eta_singular, OntoT3, set_eq_equiv, singular_eta unfold: eta, incl.
Qed.

Lemma negation : forall A B:N, eta A (neg B) <-> (Individual A /\ ~eta A B).
Proof.
intros A B;split.
- intro H;split.
  -- destruct H;assumption.
  -- solve_op_in_hyp H neg x;destruct H2.
     --- destruct H1 as [[H1 H2] H3]; intro H4;apply H2;apply rewr_singleton_in_eta with (σ:=A);solve_functor.
     --- destruct H1;contradiction.
- intro H;destruct H as [H1 H2];unfold eta;split.
  -- assumption.
  -- destruct H1 as [x H1];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- solve_op_in_goal neg;split;[
         split;[ apply N9 | intro H3;apply H2;apply rewl_singleton_in_eta with (A:=x);solve_functor ] | trivial ].
Qed.

Lemma OntoT22 : forall A, ~(eta A (neg A)).
Proof.
hauto lq: on use: negation, N1.
Qed.

Lemma OntoT23 : forall A a, eta A (neg a) -> ~(eta a A).
Proof.
sauto use: OntoT22, OntoT3 unfold: neg.
Qed.

Lemma D1 : forall A a, Individual A -> (eta A (neg a) <-> ~(eta A a)).
Proof.
strivial use: OntoT1, OntoT14, N15, OntoT23, negation, N1.
Qed.

Lemma neg_eta : forall A a, eta A (neg a) -> ~(eta A a).
Proof.
hauto use: D1 unfold: eta.
Qed.

Lemma OntoT24 : forall A a b, eta A b -> eta A a \/ eta A (neg a).
Proof.
hauto use: D1, classic unfold: eta.
Qed.

Lemma OntoT25 : forall A a, eta A a -> eta A (neg (neg a)).
Proof.
hauto lq: on use: N1, D1, N2.
Qed.

Lemma OntoT26 : forall A a, eta A (neg (neg a)) -> eta A a.
Proof.
hauto lq: on use: D1, OntoT24.
Qed.

Lemma OntoT27 : forall A a B, eta A (neg a) /\ eta B a -> eta A (neg B).
Proof.
hauto use: N17, neg_eta, negation unfold: eta.
Qed.

Lemma OntoT28 : forall A a, eta A (neg (neg a)) <-> eta A a.
Proof.
sauto use: OntoT25, OntoT26.
Qed.

Lemma OntoT29 :  forall A a B, eta B (neg a) /\ eta A a -> eta A (neg B).
Proof.
hfcrush use: OntoT27, negation, OntoT23 unfold: eta.
Qed.

Lemma OntoT30 :  forall A a B, eta B (neg A) /\ eta A a -> eta A (neg B).
Proof.
hauto lq: on use: N2, D1, N1, OntoT23.
Qed.

Lemma OntoT49 : forall a, a ⊆ a.
Proof.
sauto unfold: weakInclusion.
Qed.

Lemma OntoT51 : forall A a b c, a ⊆ b /\ b ⊆ c /\ eta A a -> eta A c.
Proof.
hfcrush use: weak_to_incl, N17 unfold: weakInclusion.
Qed.

Lemma OntoT54 : forall a b c, a ⊆ b /\ b ⊆ c -> a ⊆ c.
Proof.
hfcrush use: OntoT51 unfold: weakInclusion.
Qed.

Lemma OntoT55 : forall A a b, eta A a /\ eta A b -> ~(a ⊆ (neg b)).
Proof.
hauto lq: on use: D1, N1, N2 unfold: weakInclusion.
Qed.

Lemma D5 : forall A, eta A V <-> eta A A.
Proof.
strivial use: N1, DN1 unfold: eta.
Qed.

Lemma OntoT62 : forall A a, eta A a -> A ⊆ a.
Proof.
strivial use: weak_to_incl unfold: eta.
Qed.

Lemma OntoT66 : forall A a b, A ⊆ b /\ eta A a -> eta A b.
Proof.
sfirstorder use: N2 unfold: weakInclusion.
Qed.

Lemma OntoT67 : forall A a b, a ⊆ b /\ eta A (neg b) -> eta A (neg a).
Proof.
hauto use: D1, neg_eta unfold: weakInclusion, eta.
Qed.

Lemma OntoT68 : forall a, a ⊆ neg (neg a).
Proof.
sauto use: OntoT25 unfold: weakInclusion.
Qed.

Lemma OntoT69 : forall a, neg (neg a) ⊆ a.
Proof.
sauto use: OntoT26 unfold: weakInclusion.
Qed.

Lemma OntoT69bis : forall a, neg (neg a) ≈ a.
Proof.
sauto use: OntoT25, OntoT26 unfold: weak_eq.
Qed.

Lemma OntoT72 : forall a b, a ⊆ b -> neg b ⊆ neg a.
Proof.
sauto use: OntoT67 unfold: weakInclusion.
Qed.

Lemma OntoT74 : forall a b, b ⊆ neg a -> a ⊆ neg b.
Proof.
hauto use: OntoT54, OntoT68, OntoT72.
Qed.

Lemma OntoT75 : forall a b, neg a ⊆ b -> neg b ⊆ a.
Proof.
hauto use: OntoT54, OntoT72, OntoT69.
Qed.

Lemma OntoT78 : forall a b, neg b ⊆ neg a -> a ⊆ b.
Proof.
hauto lq: on use: negation, OntoT24 unfold: weakInclusion.
Qed.

Lemma OntoT123 : forall A, ~(eta A (neg V)).
Proof.
hauto lq: on use: D5, negation, N1 unfold: eta.
Qed.

Lemma OntoT124 : forall A, eta A V <-> exists a, eta A a.
Proof.
sauto.
Qed.

Lemma OntoT125 : forall a, a ⊆ V.
Proof.
strivial use: weak_to_incl, DN1.
Qed.

Lemma OntoT126 : forall A, eta A Λ <-> eta A (neg A).
Proof.
sfirstorder use: refl_singleton, OntoT22, OntoT8, OntoT9.
Qed.

Lemma OntoT127 : forall A, ~(eta A Λ).
Proof.
sauto use: OntoT8, OntoT9.
Qed.

Lemma OntoT129 : forall a, Λ ⊆ a.
Proof.
sfirstorder use: OntoT8, OntoT9 unfold: weakInclusion.
Qed.

Lemma OntoT130 : forall A, eta A Λ <-> eta A (neg V).
Proof.
sfirstorder use: OntoT123, OntoT8.
Qed.

Lemma OntoT131 : forall A b, eta A b -> eta A (neg Λ).
Proof.
hauto depth: 2 lq: on exh: on use: OntoT24, D6.
Qed.

Lemma OntoT133 : forall A a b, eta A a /\ eta A b -> eta A (a ∩ b).
Proof.
intros A a b H;destruct H as [H H'];assert (H0:=H);destruct H0;unfold eta;split.
- assumption.
- destruct H0 as [x H0];apply in_in_singleton with (A:=x);split.
  -- assumption.
  -- unfold In.
  hfcrush use: propositional_extensionality, eta_in_singl, singleton_impl_in, set_eq_sym, incl_equivl unfold: incl, eta, IF_then_else, n_conjunction. 
Qed.

Lemma OntoT134 : forall A a b, eta A (a ∩ b) <-> eta A a /\ eta A b.
Proof.
intros A a b;split.
- intro H;assert (H0:=H);destruct H0;destruct H0 as [x H0];cut (In (a ∩ b)x).
  -- intro H2;unfold In in H2;unfold n_conjunction in H2;unfold IF_then_else in H2;simpl in H2;cut True.
     --- intro H3;rewrite <-H2 in H3;destruct H3;[ hauto lq: on use: in_in_singleton, N11 unfold: eta | sauto ].
     --- sauto.
  -- sfirstorder use: indiv_singl_l unfold: incl.
- sauto use: OntoT133.
Qed.

Lemma OntoT135 : forall A a, eta A (a ∩ a) <-> eta A a.
Proof.
strivial use: OntoT133, OntoT134.
Qed.

Lemma OntoT136 : forall A a b, eta A (a ∩ b) <-> eta A (b ∩ a).
Proof.
hcrush use: N2, OntoT134, OntoT1.
Qed.

Lemma OntoT137 : forall A a b c, eta A (a ∩ (b ∩ c)) <-> eta A a /\ eta A b /\ eta A c.
Proof.
hcrush use: OntoT133, OntoT134 unfold: n_conjunction.
Qed.

Lemma OntoT138 : forall A a b c, eta A ((a ∩ b) ∩ c) <-> eta A a /\ eta A b /\ eta A c.
Proof.
hcrush use: OntoT134, OntoT133 unfold: n_conjunction.
Qed.

Lemma OntoT139 : forall A a b c, eta A ((a ∩ b) ∩ c) <-> eta A (a ∩ (b ∩ c)).
Proof.
hcrush use: OntoT137, OntoT138.
Qed.

Lemma OntoT140 : forall A a, ~(eta A (a ∩ (neg a))).
Proof.
hauto lq: on use: neg_eta, OntoT134 unfold: n_conjunction.
Qed.

Lemma OntoT142 : forall a b, a ∩ b ⊆ a.
Proof.
strivial use: OntoT134 unfold: weakInclusion.
Qed.

Lemma OntoT143 : forall a b, a ∩ b ⊆ b.
Proof.
strivial use: OntoT134 unfold: weakInclusion.
Qed.

Lemma OntoT144 : forall A a b c, a ⊆ b /\ a ⊆ c /\ eta A a -> eta A (b ∩ c).
Proof.
hfcrush use: OntoT133 unfold: weakInclusion.
Qed.

Lemma OntoT145 : forall a b c, a ⊆ c -> (a ∩ b) ⊆ c.
Proof.
hauto lq: on use: OntoT134 unfold: weakInclusion.
Qed.

Lemma OntoT146 : forall a b c, a ⊆ b ∩ c -> a ⊆ b.
Proof.
sauto use: OntoT142 unfold: weakInclusion.
Qed.

Lemma OntoT147 : forall a b c, a ⊆ b ∩ c -> a ⊆ c.
Proof.
sauto use: OntoT143 unfold: weakInclusion.
Qed.

Lemma OntoT148 : forall a b c, a ⊆ b /\ a ⊆ c -> a ⊆ (b ∩ c).
Proof.
hauto lq: on use: OntoT144 unfold: weakInclusion.
Qed.

Lemma OntoT149 : forall a b c, a ⊆ c -> a ∩ b ⊆ c ∩ b.
Proof.
hauto lq: on use: OntoT134, OntoT133 unfold: weakInclusion.
Qed.

Lemma Onto149bis : forall a b c, a ⊆ c -> b ∩ a ⊆ b ∩ c.
Proof.
hauto lq: on use: OntoT134, OntoT133 unfold: weakInclusion.
Qed.

Lemma OntoT150 : forall a b c, a ⊆ b ∩ c <-> a ⊆ b /\ a ⊆ c.
Proof.
strivial use: OntoT148, OntoT146, OntoT147.
Qed.

Lemma OntoT151 : forall a b, a ∩ (neg a) ⊆ b.
Proof.
sfirstorder use: OntoT140 unfold: weakInclusion.
Qed.

Lemma OntoT152 : forall a b, (neg a) ⊆ neg (a ∩ b).
Proof.
sauto use: OntoT72, OntoT142.
Qed.

Lemma OntoT153 : forall a b, a ⊆ neg ((neg a) ∩ b).
Proof.
sauto use: OntoT142, OntoT74.
Qed.

Lemma OntoT154 : forall a b, (neg b) ⊆ neg (a ∩ b).
Proof.
sauto use: OntoT143, OntoT72.
Qed.

Lemma OntoT155 : forall a b, b ⊆ neg (a ∩ (neg b)).
Proof.
sauto use: OntoT143, OntoT74.
Qed.

Lemma D8 : forall A a b, eta A (a ∪ b) <-> Individual A /\ (eta A a \/ eta A b).
Proof.
intros A a b;split.
- intro H;destruct H as [H1 H2];split.
  -- assumption.
  -- destruct H1 as [x H1];cut (In (a ∪ b)x).
     --- intro H3;unfold In in H3;unfold n_disjunction in H3;unfold IF_then_else in H3;simpl in H3;cut (True).
         ---- intro H0;rewrite <-H3 in H0;clear H3;destruct H0;[qauto use: singular_eta, N11, in_in_singleton unfold: eta | sauto ].
         ---- auto.
     --- sfirstorder use: indiv_singl_l unfold: incl.
- intro H;destruct H as [H1 H2];unfold eta;split.
  -- assumption.
  -- destruct H1 as [x H1];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- unfold In;unfold n_disjunction;unfold IF_then_else;simpl;apply propositional_extensionality;split;
         [ sauto | hauto depth: 6 lq: on drew: off use: set_eq_sym, indiv_singleton, incl_equivl unfold: eta ].
Qed.

Lemma OntoT156 : forall A a b, eta A a \/ eta A b -> eta A (a ∪ b).
Proof.
hfcrush use: N2, D8, N1 unfold: eta.
Qed.

Lemma OntoT157 : forall A a b, eta A (a ∪ b) <-> eta A a \/ eta A b.
Proof.
strivial use: D8, OntoT156.
Qed.

Lemma OntoT159 : forall A a b, eta A (a ∪ b) <-> eta A (b ∪ a).
Proof.
hcrush use: N2, OntoT157, OntoT1.
Qed.

Lemma OntoT160 : forall A a b c, eta A (a ∪ (b ∪ c)) <-> eta A a \/ eta A b \/ eta A c.
Proof.
hauto lq: on use: OntoT156, D8 unfold: n_disjunction.
Qed.

Lemma OntoT161 : forall A a b c, eta A ((a ∪ b) ∪ c) <-> eta A a \/ eta A b \/ eta A c.
Proof.
hcrush use: D8, OntoT156 unfold: n_disjunction.
Qed.

Lemma OntoT162 : forall A a b c, eta A ((a ∪ b) ∪ c) <-> eta A (a ∪ (b ∪ c)).
Proof.
hfcrush use: OntoT161, OntoT160.
Qed.

Lemma OntoT164 : forall a b, a ⊆ (a ∪ b).
Proof.
sauto use: OntoT156 unfold: weakInclusion.
Qed.

Lemma OntoT165 : forall a b, b ⊆ (a ∪ b).
Proof.
sauto use: OntoT156 unfold: weakInclusion.
Qed.

Lemma OntoT166 : forall A a b c, a ⊆ c /\ b ⊆ c /\ eta A (a ∪ b) -> eta A c.
Proof.
hcrush use: OntoT157, weak_to_incl, N17 unfold: weakInclusion.
Qed.

Lemma OntoT167 : forall a b c, a ⊆ b -> a ⊆ (b ∪ c).
Proof.
intros;unfold weakInclusion in *;intros A H';apply OntoT156;classical_left;sfirstorder.
Qed.

Lemma OntoT168 : forall a b c, (a ∪ b) ⊆ c -> a ⊆ c.
Proof.
sauto use: OntoT51, OntoT164 unfold: weakInclusion.
Qed.

Lemma OntoT169 : forall a b c, (a ∪ b) ⊆ c -> b ⊆ c.
Proof.
sauto use: OntoT165, OntoT51 unfold: weakInclusion.
Qed.

Lemma OntoT170 : forall a b c, a ⊆ c /\ b ⊆ c -> (a ∪ b) ⊆ c.
Proof.
hfcrush use: OntoT166 unfold: weakInclusion.
Qed.

Lemma OntoT172 : forall a b c, (a ∪ b) ⊆ c <-> a ⊆ c /\ b ⊆ c.
Proof.
strivial use: OntoT168, OntoT170, OntoT169.
Qed.

Lemma OntoT174 : forall a b, neg(a ∪ b) ⊆ neg a.
Proof.
sauto use: OntoT164, OntoT72.
Qed.

Lemma OntoT175 : forall a b, neg((neg a) ∪ b) ⊆ a.
Proof.
sauto use: OntoT75, OntoT164.
Qed.

Lemma OntoT176 : forall a b, neg(a ∪ b) ⊆ neg b.
Proof.
sauto use: OntoT165, OntoT72.
Qed.

Lemma OntoT177 : forall a b, neg(a ∪ (neg b)) ⊆ b.
Proof.
sauto use: OntoT75, OntoT165.
Qed.

Lemma OntoT178 : forall A a b c, eta A (a ∩ (b ∪ c)) <-> eta A a /\ (eta A b \/ eta A c).
Proof.
hcrush use: OntoT156, D8, OntoT134, OntoT133 unfold: n_conjunction, n_disjunction.
Qed.

Lemma OntoT179 : forall A a b c, eta A (a ∪ (b ∩ c)) <-> eta A a \/ (eta A b /\ eta A c).
Proof.
hcrush use: D8, OntoT134, OntoT156, OntoT133 unfold: n_disjunction, n_conjunction.
Qed.

Lemma OntoT180 : forall A a b c, eta A ((a ∩ b) ∪ (a ∩ c)) <-> ((eta A a /\ eta A b) \/ (eta A a /\ eta A c)).
Proof.
hcrush use: OntoT134, OntoT133, OntoT156, D8 unfold: n_disjunction, n_conjunction.
Qed.

Lemma OntoT181 : forall A a b c, eta A ((a ∪ b) ∩ (a ∪ c)) <-> ((eta A a \/ eta A b) /\ (eta A a \/ eta A c)).
Proof.
hcrush use: OntoT134, OntoT156, OntoT133, D8 unfold: n_conjunction, n_disjunction.
Qed.

Lemma OntoT182 : forall A a b c, eta A ((a ∩ b) ∪ (a ∩ c)) <-> eta A (a ∩ (b ∪ c)).
Proof.
hcrush use: OntoT178, OntoT180.
Qed.

Lemma OntoT183 : forall A a b c, eta A ((a ∪ b) ∩ (a ∪ c)) <-> eta A (a ∪ (b ∩ c)).
Proof.
hcrush use: OntoT179, OntoT181.
Qed.

Lemma OntoT184 : forall a b, (neg a) ∪ (neg b) ⊆ neg (a ∩ b).
Proof.
sauto use: OntoT152, OntoT154, OntoT170 unfold: n_conjunction, n_disjunction.
Qed.

Lemma OntoT186 : forall a b, a ∪ b ⊆ neg ((neg a) ∩ (neg b)).
Proof.
sauto use: OntoT153, OntoT155, OntoT170 unfold: n_conjunction, neg, n_disjunction.
Qed.

Lemma OntoT187 : forall a b, neg (a ∪ b) ⊆ ((neg a) ∩ (neg b)).
Proof.
sauto use: OntoT176, OntoT174, OntoT148.
Qed.

Lemma OntoT189 : forall a b, neg ((neg a) ∪ (neg b)) ⊆ (a ∩ b).
Proof.
sauto use: OntoT177, OntoT175, OntoT148.
Qed.

Lemma OntoT191 : forall a b, a ≈ b <-> b ≈ a.
Proof.
sauto use: weak_eq_sym.
Qed.

Lemma OntoT193 : forall a b c, a ≈ b /\ c ≈ b -> a ≈ c.
Proof.
qauto use: weak_eq_sym, weak_eq_trans.
Qed.

Lemma OntoT194 : forall a b c, b ≈ c -> a ≈ b <-> a ≈ c.
Proof.
hfcrush use: OntoT69bis, OntoT191, DO5, OntoT193, weak_eq_refl unfold: weakInclusion, weak_eq.
Qed.

Lemma OntoT197 : forall A a, a ≈ Λ -> ~(eta A a).
Proof.
sfirstorder use: OntoT8 unfold: weak_eq.
Qed.

Lemma OntoT198 : forall a, (forall A, ~(eta A a)) -> a ≈ Λ.
Proof.
hfcrush use: OntoT127 unfold: weak_eq.
Qed.

Lemma OntoT199 : forall a, (forall A, ~(eta A a)) <-> a ≈ Λ.
Proof.
sauto use: OntoT198, OntoT197, OntoT9 unfold: Λ.
Qed.

Lemma OntoT199bis : forall a, a ⊆ Λ -> a ≈ Λ.
Proof.
strivial use: OntoT129, DO5.
Qed.

Lemma OntoT200 : Λ ≈ (neg V).
Proof.
strivial use: OntoT198, DO5, OntoT191, D5, OntoT69bis, OntoT199, OntoT8, OntoT123, OntoT9 unfold: Λ, weak_eq, V.
Qed.

Lemma OntoT201 : forall a, a ≈ Λ <-> a ≈ (neg V).
Proof.
hfcrush use: OntoT9, OntoT69bis, OntoT197, OntoT124, OntoT127, D5, OntoT191, weak_eq_refl, OntoT199, OntoT123,
 OntoT198, OntoT200 unfold: weak_eq.
Qed.

Lemma OntoT203 : forall a, a ≈ neg (neg a).
Proof.
sauto use: OntoT26, OntoT25 unfold: weak_eq.
Qed.

Lemma OntoT206 : forall a b, a ≈ (neg b) <-> a ⊆ (neg b) /\ (neg a) ⊆ b.
Proof.
strivial use: OntoT75 unfold: weakInclusion, weak_eq.
Qed.

Lemma OntoT207 : forall a b, a ≈ b <-> (neg b) ⊆ (neg a) /\ (neg a) ⊆ (neg b).
Proof.
hfcrush use: DO5, OntoT78, OntoT72.
Qed.

Lemma OntoT208 : forall a b, a ≈ (neg b) <-> b ⊆ (neg a) /\ (neg a) ⊆ b.
Proof.
hfcrush use: OntoT74, OntoT206.
Qed.

Lemma OntoT209 : forall a b, a ≈ b <-> (neg a) ≈ (neg b).
Proof.
hcrush use: negation, OntoT207, D1 unfold: weakInclusion, weak_eq.
Qed.

Lemma OntoT216 : forall a b, (a ∩ b) ≈ (b ∩ a).
Proof.
hfcrush use: OntoT136 unfold: weak_eq.
Qed.

Lemma OntoT218 : forall a b, (a ∩ b) ≈ a -> a ⊆ b.
Proof.
hauto lq: on use: OntoT142, OntoT62, OntoT14, OntoT66, OntoT134, DO5 unfold: weakInclusion, weak_eq.
Qed.

Lemma OntoT219 : forall a b, a ⊆ b -> (a ∩ b) ≈ a.
Proof.
hfcrush use: DO5, weak_eq_refl, OntoT148, OntoT142 unfold: n_conjunction.
Qed.

Lemma OntoT220 : forall a b c, a ≈ b -> (c ∩ a) ≈ (c ∩ b).
Proof.
hfcrush use: DO5, Onto149bis unfold: n_conjunction.
Qed.

Lemma OntoT220bis : forall a b c, a ≈ b -> (a ∩ c) ≈ (b ∩ c).
Proof.
hfcrush use: OntoT145, OntoT143, OntoT149, DO5, OntoT148 unfold: n_conjunction.
Qed.

Lemma OntoT221 : forall a b, a ⊆ b <-> (a ∩ b) ≈ a.
Proof.
sauto use: OntoT218, OntoT219.
Qed.

Lemma OntoT222 : forall a, a ∩ V ≈ a.
Proof.
hauto use: OntoT219, OntoT124 unfold: weakInclusion.
Qed.

Lemma OntoT224 : forall a, a ∩ (neg a) ≈ Λ.
Proof.
sauto use: OntoT198, OntoT8, OntoT140, OntoT9 unfold: weak_eq, Λ.
Qed.

Lemma OntoT226 : forall a b, a ∪ b ≈ b ∪ a.
Proof.
hfcrush use: OntoT159 unfold: weak_eq.
Qed.

Lemma OntoT227bis : forall a b c, a ∪ (b ∪ c) ≈ (a ∪ b) ∪ c.
Proof.
strivial use: OntoT165, OntoT164, OntoT162, OntoT161 unfold: weakInclusion, n_disjunction, weak_eq.
Qed.

Lemma OntoT229 : forall a b, a ⊆ b -> a ∪ b ≈ b.
Proof.
hfcrush use: DO5, weak_eq_refl, OntoT170, OntoT165 unfold: n_disjunction.
Qed.

Lemma OntoT230 : forall a b c, a ≈ b -> c ∪ a ≈ c ∪ b.
Proof.
hfcrush use: OntoT157 unfold: weak_eq.
Qed.

Lemma OntoT230bis : forall a b c, a ≈ b -> a ∪ c ≈ b ∪ c.
Proof.
hfcrush use: OntoT170, OntoT167, OntoT165, DO5 unfold: n_disjunction.
Qed.

Lemma OntoT231 : forall a b, a ⊆ b <-> a ∪ b ≈ b.
Proof.
hfcrush use: DO5, OntoT229, OntoT168.
Qed.

Lemma OntoT232 : forall a, a ∪ V ≈ V.
Proof.
hauto use: OntoT229, OntoT124 unfold: weakInclusion.
Qed.

Lemma OntoT233 : forall a, a ∪ neg a ≈ V.
Proof.
intro;split;[ sauto | hfcrush use: OntoT157, OntoT24 ].
Qed.

Lemma OntoT234 : forall a, a ∪ Λ ≈ a.
Proof.
hecrush use: OntoT156, OntoT157, OntoT199, weak_eq_refl unfold: n_disjunction, weak_eq.
Qed.

Lemma OntoT234bis : forall a, Λ ∪ a ≈ a.
Proof.
sauto use: OntoT129, OntoT229.
Qed.

Lemma OntoT235 : forall a b c, (a ∩ b) ∪ (a ∩ c) ≈ a ∩ (b ∪ c).
Proof.
sauto use: OntoT182 unfold: n_disjunction, n_conjunction, weak_eq.
Qed.

Lemma OntoT236 : forall a b c, (a ∪ b) ∩ (a ∪ c) ≈ a ∪ (b ∩ c).
Proof.
sauto use: OntoT183 unfold: n_conjunction, n_disjunction, weak_eq.
Qed.

Theorem OntoT239 : forall a b, (neg a) ∪ (neg b) ≈ neg (a ∩ b).
Proof.
strivial use: OntoT189, OntoT184, OntoT206 unfold: n_disjunction, neg, n_conjunction.
Qed.

Theorem OntoT240 : forall a b, (neg a) ∩ (neg b) ≈ neg (a ∪ b).
Proof.
qauto use: OntoT153, OntoT155, OntoT74, OntoT187, DO5, OntoT170 unfold: n_disjunction, neg, n_conjunction.
Qed.

Lemma OntoT250 : forall A a, eta A a -> !A.
Proof.
sauto use: OntoT9, OntoT1, OntoT14, OntoT15, OntoT17 unfold: exists_at_least.
Qed.

Lemma OntoT262 : forall a, ~(!a) -> exists_at_most a.
Proof.
sfirstorder use: OntoT9, OntoT8, OntoT17 unfold: exists_at_most, exists_at_least.
Qed.

Lemma OntoT265 : forall A B, eta B A /\ exists_at_most A -> eta A B.
Proof.
hfcrush use: OntoT6, N16 unfold: singular_eq, exists_at_most.
Qed.

Lemma OntoT273 : forall a, (forall A B, eta A a /\ eta B a -> singular_eq A B) -> exists_at_most a.
Proof.
sauto unfold: exists_at_most.
Qed.

Lemma OntoT275 : forall A a B, eta B A /\ eta A a -> singular_eq A B.
Proof.
hfcrush use: OntoT6 unfold: singular_eq.
Qed.

Lemma OntoT282 : forall A B, eta B A /\ exists_at_most A -> singular_eq A B.
Proof.
strivial use: OntoT265 unfold: singular_eq.
Qed.

Lemma OntoT283 : forall A a B, exists_at_most a /\ eta A a /\ eta B a -> singular_eq A B.
Proof.
strivial unfold: exists_at_most.
Qed.

Lemma OntoT284 : forall a, exists_at_most a <-> (forall A B, eta A a /\ eta B a -> singular_eq A B).
Proof.
sauto.
Qed.

Lemma OntoT286 : forall A, singular_eq A A <-> exists a, eta A a.
Proof.
sfirstorder use: OntoT15, OntoT2' unfold: singular_eq.
Qed.

Lemma OntoT287 : forall A B, singular_eq A B <-> Individual A /\ eta B A.
Proof.
hcrush use: OntoT15, OntoT286, Indiv_cv, N1, N2 unfold: singular_eq.
Qed.

(*============================ Theory of Mereology ================================*)

Lemma indiv_singleton_propag : forall (Σ ϕ:N), Individual Σ /\ set_eq Σ ϕ -> Individual ϕ.
Proof.
hfcrush use: OntoT15, N1, eq_indiv_in_eta.
Qed.

Lemma N30 : forall (Φ :N)(A : object), In (el Φ) A -> In V A.
Proof.
sauto.
Qed.

Theorem N32: forall Φ Σ:N, eta Σ (el Φ) <-> (Individual Σ /\ Individual Φ /\ exists B C:object, In Σ B /\ In Φ C /\ B ≤ C).
Proof.
intros Phi Sigma;split.
- intro H;unfold eta in H;split.
  -- destruct H;assumption.
  -- split.
    + destruct H as [H H'];unfold el in H';unfold IF_then_else in H';unfold incl in H';unfold Individual in *.
      destruct H as [A H];apply singleton_impl_in in H;apply H' in H;clear H';unfold In in H;unfold caract in H;cut (True).
      ++ intro H';rewrite <-H in H';clear H;destruct H'.
        * destruct H as [H1 H2], H1 as [H H1];destruct H as [B H];exists B;assumption.
        * destruct H as [H H'];tauto.
      ++ auto.
    + unfold eta in H;destruct H as [H H'];unfold Individual in H;destruct H as [A H];assert (H0:=H);exists A;apply singleton_impl_in in H.
        unfold el in H';unfold IF_then_else in H';unfold incl in H';specialize (H' A).
        apply H' in H;clear H';unfold In in H;unfold caract in H;cut (True).
        ++ intro H';rewrite <-H in H';clear H;destruct H'.
          * destruct H as [H1 H2], H1 as [H H1].
            destruct H1 as [B H1], H1 as [C H1];destruct H1 as [H1 H3], H3 as [H3 H4].
            exists C;split.
              ** apply singleton_impl_in in H0;assumption.
              ** split.
                *** apply H3.
                *** rewrite (equiv_singleton A B) in H1;rewrite <-H1 in H4;assumption.
          * destruct H;tauto.
        ++ auto.
- intro H;destruct H as [H1 H2], H2 as [H2 H3];unfold eta;split.
  -- assumption.
  -- unfold incl;intros A H0;destruct H3 as [B H3], H3 as [C H3];destruct H3 as [H3 H4], H4 as [H4 H5];solve_op_in_goal el;split.
     + split.
       ++ assumption.
       ++ exists A, C;split.
          * apply in_singleton.
          * split.
            ** assumption.
            ** cut (Individual Sigma /\ In Sigma A).
               *** intro H6;apply indiv_singletonl in H6;rewrite <-indiv_singl_equiv in H6;destruct H6 as [H6 H7].
                      specialize (H7 B);apply H7 in H3;rewrite H3 in H5;exact H5.
               *** split;assumption.
     + auto.
Qed.

Lemma N33 : forall A B:object, eta (ι A) (el (ι B)) -> A ≤ B.
Proof.
hauto lq: on use: N32, indiv_singl_l unfold: el, set_eq.
Qed.

Lemma N34 : forall A B:object, A ≤ B -> eta (ι A) (el (ι B)).
Proof.
hauto use: in_singleton, N32, indiv_singleton.
Qed.

Lemma N35 : forall A B:object, A ≤ B <-> eta (ι A) (el (ι B)).
Proof.
sauto use: N33, N34.
Qed.

Lemma N36 : forall (σ :N)(B C :object), In σ B /\ (forall D :object, In σ D -> D ≤ C) -> In V C.
Proof.
sauto.
Qed.


Theorem N37 : forall A B :object, eta (ι A) (el (ι B)) <-> (In V A /\ In V B /\ (eta (ι B) (el (ι B)) ->
                                 forall τ σ :N, (eta (ι B) σ /\ (forall C : object, eta (ι C) τ <-> In V C /\
                                 (forall D :object, eta (ι D) σ -> eta (ι D) (el (ι C))) /\
                                  forall D :object, eta (ι D) (el (ι C)) -> exists E F:object, eta (ι E) σ /\
                                  eta (ι F)(el (ι D)) /\ eta (ι F)(el (ι E))) -> exists L :object, 
                                  set_eq τ (ι L) /\ eta (ι A)(el (ι L))))).
Proof.
intros A B;rewrite <-N35;rewrite BD;split.
- intro H;destruct H as [H1 H2], H2 as [H2 H3];split.
  -- assumption.
  -- split.
    --- assumption.
    --- intros H4 sigma to H5;rewrite <-N35 in H4;apply H3 with (β:=sigma)(α:=to) in H4;clear H3.
        destruct H5 as [H5 H6];specialize (H6 B);destruct H4 as [C H4];destruct H4 as [H3 H4].
        exists C;split;sauto use: N34.
        destruct H5 as [H5 H6];split.
        + apply DN1.
        + split.
          ++ apply DN1.
          ++ split.
             +++ sauto use: N11.
             +++ intro C;split;[ intro H7;rewrite <-In_singleton_incl_equiv in H7;cut (eta (ι C) sigma);[ intro H3;specialize (H6 C);
                 rewrite H6 in H3;clear H6;destruct H3 as [H3 H6], H6 as [H6 H8];split;[ sauto use: N10, N33 | hfcrush use: N35, eta_singl_in ] | sauto ] |
                 intro H7;destruct H7 as [H7 H8];specialize (H6 C);destruct H6;clear H;apply N12;apply H0;clear H0;split;
                 [ sauto | split;[ sauto use: N11, N34 | hfcrush use: eta_singl_in, N35 ]]].
- intro H;destruct H as [H1 H2], H2 as [H2 H3];split.
  -- assumption.
  -- split.
     --- assumption.
     --- intros H4 to sigma H5;destruct H5 as [H5 H6], H6 as [H6 H7], H7 as [H7 H8];rewrite <-N35 in H3;apply H3 with (σ:=sigma)(τ:=to) in H4.
         ---- sfirstorder use: N33.
         ---- split.
              + strivial use: N12.
              + clear H3;intro C;split.
                ++ intro H9;split.
                   +++ sauto.
                   +++ unfold eta in H9;destruct H9;rewrite In_singleton_incl_equiv in H0;specialize (H8 C);apply H8 in H0;clear H8;destruct H0 as [H8 H9];split; 
                       [ hfcrush use: singl_in_eta, N35 | hcrush use: N35, eta_singl_in ]. 
               ++ intro;specialize (H8 C);destruct H as [H3 H9], H9 as [H9 H10];unfold eta;split.
                 +++ sauto. 
                 +++ rewrite In_singleton_incl_equiv;rewrite H8;clear H8;split.
                    ++++ hfcrush use: eta_singl_in, N35.
                    ++++ intros D H11;specialize (H10 D);rewrite <-N35 in H10;apply H10 in H11;destruct H11 as [E H11], H11 as [F H11].
                         clear H9 H10;destruct H11 as [H9 H10], H10 as [H10 H11];exists E, F;split;[ strivial use: eta_singl_in | strivial use: N35 ].
Qed.


Lemma rewr_el_singleton_in_eta : forall (Σ ϕ:N)(A :object), eta Σ (el ϕ) /\ set_eq ϕ (ι A) -> eta Σ (el (ι A)).
Proof.
hauto lq: on use: in_singleton, set_eq_sym, N9, N32, in_singleton_eq unfold: eta.
Qed.

Lemma rewl_el_singleton_in_eta : forall (Σ ϕ:N)(A :object), eta Σ (el (ι A)) /\ set_eq ϕ (ι A) -> eta Σ (el ϕ).
Proof.
hauto lq: on use: set_eq_sym, equiv_singleton, N32, indiv_singl_equiv, singular_eta unfold: eta.
Qed.

Lemma N38 : forall δ σ : N, (exists Ψ θ : N, eta Ψ σ /\ eta θ (el δ) /\ eta θ (el Ψ)) ->
                               exists E F : object, eta (ι E) σ /\ eta (ι F) (el δ) /\ eta (ι F) (el (ι E)).
Proof.
qauto depth: 4 l: on use: N33, rewr_el_singleton_in_eta, N9, eta_singular, set_eq_sym, incl_equivl, 
rewr_singleton_in_eta unfold: set_eq, incl, eta, Individual.
Qed.


Lemma N39b : forall δ σ : N, (exists E F : object, eta (ι E) σ /\ eta (ι F) (el δ) /\ eta (ι F) (el (ι E))) ->
                              (exists Ψ θ : N, eta Ψ σ /\ eta θ (el δ) /\ eta θ (el Ψ)).
Proof.
sauto.
Qed.

Lemma N39 : forall δ σ : N, (exists Ψ θ : N, eta Ψ σ /\ eta θ (el δ) /\ eta θ (el Ψ)) <->
                               exists E F : object, eta (ι E) σ /\ eta (ι F) (el δ) /\ eta (ι F) (el (ι E)).
Proof.
intros;split;[ apply N38 | apply N39b ].
Qed.

Theorem N41 :forall A B, eta A (el B) <-> (eta A A /\ eta B B /\ (eta B (el B) -> (forall C a, eta B a /\ 
                            (forall D, eta D C <-> (forall E :N, eta E a -> eta E (el D)) /\ (forall E, eta E (el D) ->
                                               exists F G, eta F a /\ eta G (el E) /\ eta G (el F))) -> eta A (el C)))).
Proof.
intros Sigma Phi;split.
- intro H;split. 
  -- apply N2 with (σ:=el Phi);assumption.
  -- split.
     --- rewrite N32 in H;destruct H as [H1 H2], H2 as [H2 H3];unfold eta;split.
         ---- assumption.
         ---- apply incl_refl.
     --- intros H' sigma to H0;destruct H0 as [H1 H2];assert (H0:=H);apply N2 in H;rewrite N1 in H;apply N2 in H';rewrite N1 in H';unfold Individual in *.
         destruct H as [A H], H' as [B H'];cut (eta (ι A) (el Phi)).
         ---- intro H3;cut (eta (ι A) (el (ι B))).
              + intro H4;rewrite N37 in H4;destruct H4 as [H4 H5], H5 as [H5 H6];clear H3 H4 H5;rewrite <-N35 in H6;cut (B ≤ B).
                ++ intro H7;apply H6 with (τ:=sigma)(σ:=to) in H7;clear H6.
                  +++ destruct H7 as [C H7];destruct H7 as [H3 H7];cut (eta Sigma (el (ι C))).
                      ++++ intro H4;apply rewl_el_singleton_in_eta with (A:=C);split;assumption.
                      ++++ apply rewl_singleton_in_eta with (A:=A);solve_functor.
                  +++ split.
                     ++++ apply rewr_singleton_in_eta with (σ:=Phi);solve_functor.
                     ++++ intro C;split.
                          * intro H3;split.
                            ** apply univ.
                            ** specialize (H2 (ι C));rewrite H2 in H3;destruct H3 as [H3 H5];split.
                              *** intros D H4;specialize (H3 (ι D));apply H3;assumption.
                              *** intros D H4;specialize (H5 (ι D));apply H5 in H4;clear H5;rewrite <-N39;auto.
                          * intro H3;specialize (H2 (ι C));destruct H3 as [H3 H4];clear H3;destruct H4 as [H3 H4].
                            rewrite H2;split.
                            ** intros delta H5;assert (H6:=H5);apply N2 in H6;rewrite N1 in H6;unfold Individual in H6.
                               destruct H6 as [D H6];cut (eta (ι D) to). 
                               *** specialize (H3 D);intro H8;apply H3 in H8;apply rewl_singleton_in_eta with (A:=D);solve_functor.
                               *** apply rewr_singleton_in_eta with (σ:=delta);solve_functor.
                            ** intros delta H5;assert (H6:=H5);apply N2 in H6;rewrite N1 in H6;unfold Individual in H6.
                               destruct H6 as [D H6];cut (eta (ι D) (el (ι C))).
                               *** specialize (H4 D);intro H8;apply H4 in H8;destruct H8 as [E H8], H8 as [F H8];exists (ι E), (ι F).
                                   destruct H8 as [H8 H9], H9 as [H9 H10];split.
                                   **** assumption.
                                   **** split.
                                        ***** apply rewl_el_singleton_in_eta with (A:=D);solve_functor.
                                        ***** assumption.
                               *** apply rewr_singleton_in_eta with (σ:=delta);solve_functor.
                ++ apply le_object_refl.
              + apply rewr_el_singleton_in_eta with (ϕ:=Phi);solve_functor.
        ---- apply rewr_singleton_in_eta with (σ:=Sigma);solve_functor.
- intro H;destruct H as [H1 H2], H2 as [H2 H3];rewrite N32;split.
  -- rewrite <-N1;assumption.
  -- split.
     --- rewrite <-N1;assumption.
     --- rewrite N1 in H1;unfold Individual in H1;rewrite N1 in H2;unfold Individual in H2;destruct H1 as [A H1], H2 as [B H2].
         exists A, B;split.
         ---- unfold set_eq in H1;specialize (H1 A);rewrite <-H1;apply in_singleton.
         ---- split.
              ----- unfold set_eq in H2;specialize (H2 B);rewrite <-H2;apply in_singleton.
              ----- rewrite N35;rewrite N37;split.
                + apply univ.
                + split.
                   ++ apply univ.
                   ++ intro H4;cut (eta Phi (el (ι B))).
                       +++ intro H5;cut (eta Phi (el Phi)).
                            ++++ intro H6;clear H4 H5;intros sigma to H4;apply H3 with (a:=to)(C:=sigma) in H6;clear H3.
                                  +++++ destruct H4 as [H4 H5];rewrite N32 in H6;destruct H6 as [H6 H7], H7 as [H7 H8];unfold Individual in H7.
                                        destruct H7 as [C H7];assert (H0:=H7);apply eta_singleton_l in H7;specialize (H5 C);apply H5 in H7;clear H5.
                                        destruct H7 as [H7 H9], H9 as [H9 H10];clear H7;specialize (H9 B);apply H9 in H4;clear H9. 
                                        exists C;split.
                                      * symmetry;assumption.
                                      * apply N32;split.
                                        ** rewrite indiv_singleton;auto.
                                        ** split.
                                           *** rewrite indiv_singleton;auto.
                                           *** destruct H8 as [E H8], H8 as [F H8];destruct H8 as [H8 H3], H3 as [H3 H5];exists E, F;split.
                                                **** rewrite <-H1 in H8;assumption.
                                                **** split;[ rewrite <-H0 in H3;assumption | assumption ].
                                  +++++ destruct H4 as [H4 H5];split.
                                        * apply rewl_singleton_in_eta with (A:=B);solve_functor.
                                        * intro Gamma;split.
                                          ** intro H7;assert (H0:=H7);apply N2 in H0;rewrite N1 in H0;unfold Individual in H0;destruct H0 as [C H0];cut (eta (ι C) sigma).
                                             *** intro H3;specialize (H5 C);apply H5 in H3;clear H5;destruct H3 as [H3 H5], H5 as [H5 H8].
                                                 clear H3;split.
                                                 **** intros delta H3. assert (H10:=H3);apply N2 in H10;rewrite N1 in H10;unfold Individual in H10;destruct H10 as [D H10];cut (eta (ι D) to).
                                                      ***** intro H9;specialize (H5 D);apply H5 in H9;clear H5;cut (eta (ι D) (el Gamma)).
                                                            ****** intro H11;apply rewl_singleton_in_eta with (A:=D);solve_functor.
                                                            ****** apply rewl_el_singleton_in_eta with (A:=C);solve_functor.
                                                      ***** apply rewr_singleton_in_eta with (σ:=delta);solve_functor.
                                                 **** intros delta H3. assert (H10:=H3);apply N2 in H10;rewrite N1 in H10;unfold Individual in H10;destruct H10 as [D H10];cut (eta (ι D)(el Gamma)).
                                                      ***** intro H11;specialize (H8 D);cut (eta (ι D) (el (ι C))).
                                                            ****** intro H12;apply H8 in H12;clear H5 H8;destruct H12 as [E H12], H12 as [F H12];destruct H12 as [H5 H8], H8 as [H8 H12].
                                                                   exists (ι E), (ι F);split.
                                                                   ******* assumption.
                                                                   ******* split;[ apply rewl_el_singleton_in_eta with (A:=D);solve_functor | assumption].
                                                            ****** apply rewr_el_singleton_in_eta with (ϕ:=Gamma);solve_functor.
                                                      ***** apply rewr_singleton_in_eta with (σ:=delta);solve_functor.
                                            *** apply rewr_singleton_in_eta with (σ:=Gamma);solve_functor.
                                          ** intro H3;destruct H3 as [H3 H7];assert (H0:=H3);specialize (H3 (ι B));apply H3 in H4;rewrite N32 in H4;destruct H4 as [H4 H8], H8 as [H8 H9].
                                             unfold Individual in H8;destruct H8 as [C H8];specialize (H5 C);destruct H5;destruct H5.
                                             *** split.
                                                 **** apply univ.
                                                 **** split.
                                                      ***** intros D H10;specialize (H0 (ι D));apply H0 in H10;clear H0;apply rewr_el_singleton_in_eta with (ϕ:=Gamma);solve_functor.
                                                      ***** intros D H10;specialize (H7 (ι D));cut (eta (ι D) (el Gamma)).
                                                            ****** intro H5;apply H7 in H5;clear H H3 H7;destruct H5 as [Psi H5], H5 as [delta H5];destruct H5 as [H5 H11], H11 as [H11 H12].
                                                                   assert (H13:=H5);apply N2 in H13;rewrite N1 in H13;unfold Individual in H13;destruct H13 as [E H13].
                                                                   assert (H14:=H12);apply N2 in H14;rewrite N1 in H14;unfold Individual in H14;destruct H14 as [F H14];exists E, F;split.
                                                                   ******* apply rewr_singleton_in_eta with (σ:=Psi);solve_functor.
                                                                   ******* split.
                                                                           ******** apply rewr_singleton_in_eta with (σ:=delta);solve_functor.  
                                                                           ******** cut (eta delta (el (ι E)));[ intro;apply rewr_singleton_in_eta with (σ:=delta);solve_functor |
                                                                                     apply rewr_el_singleton_in_eta with (ϕ:=Psi);split;[ assumption | sfirstorder ]].
                                                            ****** clear H;apply rewl_el_singleton_in_eta with (A:=C);solve_functor.
                                            *** cut (eta (ι C) sigma);[ intro;apply rewl_singleton_in_eta with (A:=C);split;sfirstorder | sauto ]. 
                           ++++ apply rewl_el_singleton_in_eta with (A:=B);sfirstorder. 
                       +++ apply rewl_singleton_in_eta with (A:=B);solve_functor.
Qed.


(** MEREOLOGY **)


Lemma Part : forall A B, eta A (pt B) <-> eta A (el B) /\ ~(A ≡ B).
Proof.
intros A B;split.
- intro H;solve_op_in_hyp H pt x;destruct H2.
  -- destruct H1 as [[H2 [H3 H4]] H1];split;[ qauto use: in_in_singleton, N11, singular_eta unfold: eta |
         qauto use: N1, N10, Indiv_cv, singular_eta, indiv_singl_l, singular_eq_eq_obj unfold: singular_eq ].
  -- destruct H1;contradiction.
- intro H;destruct H as [H1 H2];assert (H10:=H1);unfold eta in H1;destruct H1 as [H0 H1];unfold eta;split.
  -- assumption.
  -- destruct H0 as [x H0];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- solve_op_in_goal pt;split.
         ---- split;[ sauto | split;[ hfcrush use: indiv_singl_l, N10 unfold: incl | qauto depth: 4 l: on use: OntoT6, 
                           OntoT15, eta_singleton_l, N41, rewl_singleton_in_eta unfold: singular_eq ]].
         ---- auto.
Qed.

Lemma Exterior : forall A B, eta A (ext B) <-> (Individual A /\ Individual B /\ ~(exists C, eta C (el B) /\ eta C (el A))).
Proof.
intros A B;split.
- intro H;assert (H':=H);solve_op_in_hyp H ext x;destruct H2.
  -- destruct H1 as [[H2 [H3 H4]] H1];split.
     --- destruct H';assumption.
     --- split.
         ---- assumption.
         ---- intro H5;destruct H5 as [C [H6 H7]];apply H4;exists C;split;[ assumption | apply rewr_el_singleton_in_eta with (ϕ:=A);sfirstorder ].
  -- destruct H1;contradiction.
- intro H;destruct H as [H1 [H2 H3]];unfold eta;split.
  -- assumption.
  -- destruct H1 as [x H1];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- solve_op_in_goal ext;split.
         ---- split.
              ----- apply N9.
              ----- split;[ assumption |
                    intro H4;destruct H4 as [C [H4 H5]];apply H3;exists C;split;[ assumption | apply rewl_el_singleton_in_eta with (A:=x);
                    split;[ assumption | apply set_eq_sym;assumption ]]].
         ---- auto.
Qed.

Lemma relatComp : forall P Q R :N, eta P (relCompl Q R) <-> Individual P /\ eta Q (SubColl R) /\ eta P (klass ((el R) ∩ (ext Q))).
Proof.
intros P Q R;split.
- intro H;destruct H as [H1 H2];split.
  -- assumption.
  -- destruct H1 as [x H1];assert (H3:set_eq (ι x) P /\ incl P (relCompl Q R)).
     --- split;assumption.
     --- apply incl_in_singleton in H3;unfold In in H3;unfold relCompl in H3;unfold IF_then_else in H3;simpl in H3;assert (H4:True).
         ---- auto.
         ---- rewrite <-H3 in H4;destruct H3;destruct H4.
              ----- destruct H as [[H4 [H5 H6]] H3];split.
                    ------ assumption.
                    ------ apply rewl_singleton_in_eta with (A:=x);split;[assumption | apply set_eq_sym;assumption ].
              ----- destruct H;contradiction.
- intro H;destruct H as [H1 [H2 H3]];unfold eta;split.
  -- assumption.
  -- destruct H1 as [x H1];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- unfold In;unfold relCompl;unfold IF_then_else;simpl;apply propositional_extensionality;split.
         ---- intro;auto.
         ---- intro;left;split.
              ----- split;[ apply N9 |
                    split;[ assumption | apply rewr_singleton_in_eta with (σ:=P);split;[ assumption | apply set_eq_sym;assumption ]]].
              ----- auto.
Qed.

Definition eta_inv a b := eta b a.

Add Parametric Morphism (B :N) : (eta_inv B) with signature (set_eq) ==> (iff) as eta_singleton.
Proof.
hfcrush use: eq_indiv_in_eta, set_eq_sym unfold: eta_inv.
Qed.

Ltac subst_set_eq_in_hyp H fc z :=
 match type of H with
      | set_eq ?X ?Y => let H15 := fresh in assert (H15:=H);apply eta_singleton with (B:=fc z) in H15;unfold eta_inv in H15
end.

Add Parametric Morphism (A:N): (eta A) with signature (set_eq) ==> (iff) as ext_plur.
Proof.
hauto lq: on use: incl_equiv, set_eq_sym unfold: eta.
Qed.

Definition Phi_singl (E1 :N -> N -> Prop)(E2 :N)(E3 :N) := (E1 E2) E3.

Add Parametric Morphism (A:N): (Phi_singl eta_inv A) with signature (set_eq) ==> (iff) as eta_inv_singleton.
Proof.
intros X Y H;unfold Phi_singl;unfold eta_inv;apply eta_singleton;assumption.
Qed.


Lemma rewr_pt_singleton_in_eta : forall (Σ ϕ :N)(A :object), eta Σ (pt ϕ) /\ set_eq ϕ (ι A) -> eta Σ (pt (ι A)).
Proof.
intros sigma phi A [H H'];rewrite Part in *;destruct H as [H1 H2];split.
- sauto use: rewr_el_singleton_in_eta.
- intro H3;apply H2;clear H2;hauto lq: on use: in_singleton, N10, rewl_singleton_in_eta, singular_eq_eq_obj unfold: set_eq, ι, singular_eq.
Qed.

Lemma rewl_pt_singleton_in_eta : forall (Σ ϕ :N)(A :object), eta Σ (pt (ι A)) /\ set_eq ϕ (ι A) -> eta Σ (pt ϕ).
Proof.
intros sigma phi A [H H'];rewrite Part in *;destruct H as [H1 H2];split.
- apply rewl_el_singleton_in_eta with (A:=A);sfirstorder. 
- intro H3;apply H2;destruct H1;assert (Individual phi).
  -- unfold Individual;exists A;apply set_eq_sym;assumption.
  -- apply singular_eq_trans with (B:=phi);split;[ assumption |
     assert (Individual phi /\ Individual (ι A));[ sauto | apply singular_eq_dec in H4;sfirstorder ]].
Qed.

Lemma rewl_ext_singleton_in_eta : forall (Σ ϕ :N)(A :object), eta Σ (ext (ι A)) /\ set_eq ϕ (ι A) -> eta Σ (ext ϕ).
Proof.
intros sigma phi A [H H'];rewrite Exterior in *;destruct H as [H1 [H2 H3]];destruct H2 as [x H2];split.
- assumption.
- split.
  -- unfold Individual;exists A;firstorder.
  -- intros H4;destruct H4 as [B [H4 H5]];apply H3;exists B;split;[ apply rewr_el_singleton_in_eta with (ϕ:=phi);sfirstorder | sauto ]. 
Qed.

Lemma rewr_ext_singleton_in_eta : forall (Σ ϕ :N)(A :object), eta Σ (ext ϕ) /\ set_eq ϕ (ι A) -> eta Σ (ext (ι A)).
Proof.
intros sigma phi A [H H'];rewrite Exterior in *;destruct H as [H1 [H2 H3]];destruct H2 as [x H2];split.
- assumption.
- split.
  -- apply N9.
  -- intro H5;destruct H5 as [B [H4 H5]];apply H3;exists B;split;[ apply rewl_el_singleton_in_eta with (A:=A);sfirstorder | assumption ].
Qed.

Ltac subst_set_eq_f H ft z P :=
match type of H with
      | set_eq ?X ?Y => match ft with
         | ext => let H20 := fresh in assert (H20 :eta P (ext X) <-> eta P (ext Y));[split;[ intro H21;
         apply rewl_ext_singleton_in_eta with (A:=z);split;[assumption | apply set_eq_sym;assumption] |
          intro H21;apply rewr_ext_singleton_in_eta with (ϕ:=Y);split;[assumption | apply set_eq_sym;assumption] ] | ]
         | el => let H20 := fresh in assert (H20 :eta P (el X) <-> eta P (el Y));[split;[ intro H21;
         apply rewl_el_singleton_in_eta with (A:=z);split;[assumption | apply set_eq_sym;assumption] |
          intro H21;apply rewr_el_singleton_in_eta with (ϕ:=Y);split;[assumption | apply set_eq_sym;assumption] ] | ]
         | pt => let H20 := fresh in assert (H20 :eta P (pt X) <-> eta P (pt Y));[split;[ intro H21;
         apply rewl_pt_singleton_in_eta with (A:=z);split;[assumption | apply set_eq_sym;assumption] |
          intro H21;apply rewr_pt_singleton_in_eta with (ϕ:=Y);split;[assumption | apply set_eq_sym;assumption] ] | ]
         end
end.


(* ========================== theorems for Collective classes ================================== *)


Lemma MieT1 : forall A a, eta A (klass a) -> eta A A.
Proof.
strivial use: N1 unfold: eta.
Qed.

Lemma MieT9 : forall A B, eta A (el B) -> Individual B.
Proof.
strivial use: N32.
Qed.

Lemma Element : forall A B, eta A (el B) -> (Individual B /\ exists C D, In A C /\ In B D /\ C ≤ D).
Proof.
strivial use: N32, MieT9.
Qed.


Lemma Klass : forall A a, eta A (klass a) <-> (Individual A /\ (forall B, eta B a -> eta B (el A)) /\
                                              (forall B, eta B (el A) -> exists C D, eta C a /\ eta D (el C) /\ eta D (el B))).
Proof.
intros A a;split.
- intro H1;assert (H20:=H1);solve_op_in_hyp H1 klass x;destruct H2.
  -- destruct H0 as [[H2 [H4 H5]] H0];split.
     --- sauto.
     --- split.
         ---- intros B H6;apply rewl_el_singleton_in_eta with (A:=x);split;[ apply H4;firstorder | sfirstorder ]. 
         ---- intros C H7;cut (eta C (el A) /\ set_eq A (ι x));[
              intros [H6 H8];apply H5;apply rewr_el_singleton_in_eta with (ϕ:=A);sfirstorder | sfirstorder ].
  -- destruct H0;contradiction.
- intro H;destruct H as [H0 [H1 H2]];unfold eta;split.
  -- assumption.
  -- destruct H0 as [x H0];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- solve_op_in_goal klass;split.
         ---- split. 
              + apply N9.
              + split. 
                ++ intros B H6;apply H1 in H6;apply rewr_el_singleton_in_eta with (ϕ:=A);sfirstorder. 
                ++ intros B H4;apply H2;apply rewl_el_singleton_in_eta with (A:=x);sfirstorder.
         ---- auto.
Qed.

Lemma MieT3 : forall (A B a : N), eta A (klass a) -> eta B a -> eta B (el A).
Proof.
hfcrush use: Klass.
Qed.

Lemma MieT4 : forall (A B a : N), eta A (klass a) -> eta B (el A) -> exists C D, eta C a /\ eta D (el C) /\ eta D (el B).
Proof.
hfcrush use: Klass unfold: el, klass.
Qed.


(** identical to MieT6 **)

Lemma SinXIX : forall (A a : N), eta A a -> eta A (el A).
Proof.
hauto lq: on use: N2, N41.
Qed.

(** identical to MieT7 **)

Lemma part : forall A B, eta A (pt B) <-> (eta A (el B) /\ ~(set_eq B A)).
Proof.
hfcrush use: Part, MieT9, set_eq_sym, singular_eq_dec unfold: eta.
Qed.

Lemma MieT7 : forall (A :N), eta A A -> eta A (el A). 
Proof.
hauto lq: on use: N41.
Qed.

Lemma MieT8 : forall (A a : N), eta A (klass a) -> eta A (el A).
Proof.
sfirstorder use: N1, MieT7, Klass.
Qed.

Lemma MieT10 : forall (A a:N), eta A a -> eta A (klass A).
Proof.
intros A a H;rewrite Klass;split.
- destruct H;assumption.
- split;[ sfirstorder use: incl_refl, MieT7 unfold: eta, incl | intros B H1;exists A, B;hauto lq: on use: N2, N41 ].
Qed.

Lemma MieT11 : forall (A:N), eta A A -> eta A (klass A).
Proof.
sauto use: MieT10.
Qed.

Lemma MieT12 : forall (A:N), eta A A <-> eta A (klass A).
Proof.
sfirstorder use: N1, MieT11, Klass.
Qed.

Lemma MieT14 : forall (a:N), eta (klass a)(klass a) -> eta (klass a) (el (klass a)).
Proof.
sauto use: MieT7.
Qed.

Lemma MieT15 : forall B C, (eta B C /\ eta C B) -> (forall A, eta A B <-> eta A C).
Proof.
sfirstorder use: N5.
Qed.

Lemma MieT16 : forall A B C, eta A (klass B) /\ set_eq B C -> eta A (klass C).
Proof.
intros A B C H;destruct H as [H H'];rewrite Klass in H;destruct H as [H0 [H1 H2]];rewrite Klass.
split.
- assumption. 
- split.
  -- hauto use: N22 unfold: el.
  -- intros D H;apply H2 in H;destruct H as [F [G [H5 [H6 H7]]]];exists F, G;strivial use: N22 unfold: el.
Qed.

Lemma MieT18 : forall A B C, eta A (el B) /\ set_eq B C -> eta A (el C).
Proof.
intros A B C [H H'];assert (H0:=H);apply MieT9 in H0;destruct H0 as [x H0];assert (set_eq (ι x) C).
- apply set_eq_trans with (y:=B);assumption.
- subst_set_eq_f H1 el x A;rewrite <-H2;apply rewr_el_singleton_in_eta with (ϕ:=B);split;[ assumption | apply set_eq_sym;assumption ].
Qed.

Lemma MieT17 : forall A B C, eta A (pt B) /\ set_eq B C -> eta A (pt C).
Proof.
intros A B C [H1 H2];rewrite part in *;destruct H1 as [H1 H3];split;[ sauto use: MieT18 | sfirstorder ]. 
Qed.

Lemma SinII : forall P, Individual P -> eta P (el P).
Proof.
sfirstorder use: N1, MieT7.
Qed.

Lemma SinVII : forall A a, eta A a -> eta A (klass (el A)).
Proof.
intros Phi a H;rewrite Klass;split;[ sauto | hfcrush use: SinXIX, SinII unfold: eta ].
Qed.

(** identical to MieT21 **)

Lemma SinX : forall P Q, eta P (el Q) -> eta Q (klass (el Q)).
Proof.
hauto lq: on use: N41, SinVII.
Qed.

Lemma SinXVIII : forall P Q, eta P (pt Q) -> eta P (el Q).
Proof.
strivial use: Part.
Qed.

Lemma SinLI : forall P Q, eta P (el Q) /\ eta Q (el P) -> set_eq P Q.
Proof.
intros P Q H;destruct H as [H H'];apply Element in H;apply Element in H';destruct H as [H1 H2], H' as [H3 H4];destruct H2 as [x [y [H2 [H5 H6]]]].
destruct H4 as [x' [y' [H4 [H7 H8]]]];destruct H1 as [z H1], H3 as [z' H3];rewrite <-H1;rewrite <-H3;rewrite ind_seq_equiv;rewrite <-H1 in H5, H4.
rewrite <-H3 in H2, H7;rewrite equiv_singleton in H2, H5, H4, H7;rewrite <-H2 in H6;rewrite <-H5 in H6;rewrite <-H4 in H8;rewrite <-H7 in H8.
apply le_object_antisym;split;assumption.
Qed.

(** identical to MieT20 **)

Lemma SinXXIII : forall P Q R, eta P (el Q) /\ eta Q (el R) -> eta P (el R).
Proof.
intros Phi sigma to H;destruct H as [H1 H2];unfold eta in *;destruct H1 as [H1 K1], H2 as [H2 K2];split.
- assumption.
- unfold incl in *;intros A H;specialize (K1 A);unfold Individual in H1;destruct H1 as [E H1];cut (set_eq (ι E) Phi /\ In Phi A).
  -- intro K0;apply in_singleton_eq in K0;rewrite K0 in H1;clear K0;apply K1 in H;unfold el in H;unfold IF_then_else in H;simpl in H;cut (True).
     --- intro H0;rewrite <-H in H0;clear H;destruct H0.
         ---- destruct H as [H K], H as [H H3];destruct H3 as [B H3], H3 as [C H3];destruct H3 as [H3 H4], H4 as [H4 H5];rewrite equiv_singleton in H3.
              rewrite <-H3 in H5;clear H3;unfold Individual in H;destruct H as [D H];cut (set_eq (ι D) sigma /\ In sigma C).
              ----- intro K0;apply in_singleton_eq in K0;rewrite K0 in H;clear E K0;specialize (K2 C);apply K2 in H4;unfold el in H4;unfold IF_then_else in H4;simpl in H4.
                    rewrite <-H4 in K;clear H4;destruct K.
                    + destruct H0 as [H0 K3], H0 as [H0 H6];destruct H6 as [E H6], H6 as [F H6];destruct H6 as [H6 H7], H7 as [H7 H8];rewrite equiv_singleton in H6.
                      rewrite <-H6 in H8;solve_op_in_goal el;split.
                         +++ split.
                             ++++ assumption.
                             ++++ exists A, F;split.
                                  +++++ apply in_singleton.
                                  +++++ split.
                                        ++++++ assumption.
                                        ++++++ apply le_object_transitive with (B:=C);split;assumption.
                         +++ auto.
                    + destruct H0;contradiction.
              ----- split;assumption.
         ---- destruct H;contradiction.
     --- auto.
  -- split;assumption.
Qed.

(** foundational theorems **)

Lemma LejT0 :  forall A B, Individual A -> eta A (el B) <-> eta A (pt B) \/ set_eq B A.
Proof.
intros A B H0;split;[ intro;rewrite part;tauto | hfcrush use: MieT18, SinII, Part, set_eq_sym ].
Qed.

Lemma LejT1 : forall A a, eta A a -> exists B, eta B (el A).
Proof.
hfcrush use: MieT18, SinII, Part, set_eq_sym.
Qed. 

Lemma LejT2 : forall A B a, eta B a /\ (forall C, eta C a -> eta C (el A)) /\ (forall C, eta C (el A) -> exists D E, eta D a /\ eta E (el D) /\ eta E (el C)) -> eta A (klass a).
Proof.
intros A B a H;destruct H as [H1 [H2 H3]];assert (H0:=H1);apply H2 in H1;apply MieT9 in H1;rewrite Klass;split;[ assumption | sauto ]. 
Qed.

Lemma LejT3 : forall A B, eta A (el B) -> exists C D, eta C B /\ eta D (el A) /\ eta D (el C).
Proof.
intros A B H;exists B, A;hauto lq: on use: N41.
Qed.

Lemma LejT11 : forall E a, eta E a -> (forall A, eta A (klass a) <-> ((forall B, eta B a -> eta B (el A)) /\ (forall B, eta B (el A) -> exists C D, eta C a /\ eta D (el B) /\ eta D (el C)))).
Proof.
intros E a H A;split;[ hcrush use: MieT4, Klass | intro H';destruct H';rewrite Klass;split;[ hauto lq: on use: Element | hfcrush ]].
Qed.

Lemma LejT12 : forall A B a, eta A (el B) /\ eta B a -> eta A (el (klass a)).
Proof.
intros A B a H;destruct H as [H1 H2];rewrite N41 in H1;destruct H1 as [H1 [H3 H4]];rewrite N1 in H3;apply SinII in H3.
apply H4 with (C:=klass a)(a:=a) in H3;[ assumption | split;[auto | hfcrush use: LejT11]]. 
Qed.

(** identical to MieT13 **)

Lemma LejT13 : forall A a, eta A a -> eta (klass a)(klass a).
Proof.
hfcrush use: N1, SinXIX, LejT12, MieT9.
Qed.

Lemma MieT22 : forall A a:N, eta A a -> eta A (el (klass a)).
Proof.
sauto use: SinXIX, LejT12.
Qed.

Theorem klExistence : forall (A a :N), eta A a -> exists B, eta B (klass a).
Proof.
sauto use: LejT13.
Qed.

Lemma MieT2 : forall (A a : N), eta A (klass a) -> exists B, eta B a.
Proof.
hfcrush use: Klass, MieT8 unfold: el, klass.
Qed.

(** A and klass of a's are identical **)

Lemma MieT24 : forall A a:N, eta A (klass a) -> A ≡ (klass a).
Proof.
hauto depth: 2 lq: on exh: on use: MieT2, LejT13, MieT11, OntoT6 unfold: klass, singular_eq.
Qed.

Lemma MieT24' : forall A a:N, A ≡ (klass a) -> eta A (klass a).
Proof.
sauto.
Qed.

Theorem klUniq : forall A B a, eta A (klass a) /\ eta B (klass a) -> A ≡ B.
Proof.
hauto depth: 2 lq: on exh: on use: N5, MieT24 unfold: singular_eq.
Qed.


Lemma MieT23 : forall A B a:N, eta A (klass B) /\ eta B a -> A ≡ B.
Proof.
hfcrush use: MieT10, klUniq.
Qed.

Lemma MieT25 : forall a, !a <-> !klass a.
Proof.
strivial use: OntoT8, klExistence, MieT2, OntoT17 unfold: exists_at_least.
Qed.

Lemma MieT26 : forall A a, eta A (klass a) -> eta A (klass (klass a)).
Proof.
hauto lq: on use: N5, MieT24, MieT11 unfold: singular_eq, incl, klass, eta.
Qed.

Lemma MieT27 : forall A a, eta A (klass (klass a)) -> eta A (klass a).
Proof.
intros A a H;assert (H0:=H);assert (H10:=H);apply SinXIX in H;apply MieT4 with (B:=A) in H0.
- destruct H0 as [C [D [H0 [H1 H2]]]];assert (H4:=H0);apply MieT24 in H0;apply singular_eq_eq_obj in H0;apply set_eq_sym in H0;assert (H3:eta A (klass C)).
  -- apply MieT16 with (B:=klass a);sfirstorder.
  -- assert (H6:=H4);apply N2 in H4;assert (H5:singular_eq A C);[ apply MieT23 with (a:=C);sfirstorder | sfirstorder ].
- auto.
Qed.

(** class of a and class of class of a denote the same object unlike set theory **)

Lemma MieT27bis :  forall A a, eta A (klass (klass a)) <-> eta A (klass a).
Proof.
sauto use: MieT26, MieT27.
Qed.

Lemma MieT28 : ~forall A a, eta A (klass a).
Proof.
intro H;specialize (H Λ Λ);sfirstorder use: N1, OntoT9 unfold: eta.
Qed.

(** a class built on the empty name does not exist **)

Lemma MieT29 : forall A, ~eta A (klass Λ).
Proof.
hauto lq: on use: MieT2, D6.
Qed.

(** supplementary theorems **)


Lemma MieT30 :forall a b, (exists F, eta F a) /\ (exists G, eta G b) /\ weak_eq (el (klass a))(el (klass b)) -> forall B, eta B (klass a) -> eta B (klass b).
Proof.
intros a b H B H';destruct H as [H1 H2], H2 as [H2 H3];assert (K1:=H');apply OntoT14 in H';destruct H1 as [A H1];apply LejT13 in H1.
apply MieT14 in H1;cut (eta B (el (klass a))).
- intro K2;unfold weak_eq in H3;assert (H4:=H3);specialize (H3 B);assert (K0:=H2);destruct H2 as [C H2];apply LejT13 in H2;rewrite H3 in K2;clear H3.
   -- destruct K0 as [E K0];cut (eta (klass b)(klass b) -> eta E b).
      --- intro K4;apply MieT3 with (A:=klass b) in K4.
          ---- assert (K8:=H4);specialize (H4 E);rewrite <-H4 in K4;assert (K5:=K1);apply MieT24 in K1;unfold eta;split.
               ----- rewrite <-N1;assumption. 
               ----- destruct H';destruct H as [D H];unfold incl;intros F H5;rewrite <-H in H5;rewrite equiv_singleton in H5.
                     rewrite <-H5;assert (K6:=K0);destruct K0;destruct H3 as [J H3];solve_op_in_goal klass; split.
                          +++ split.
                              ++++ apply N9. 
                              ++++ split.
                                   +++++ intros I K7;specialize (K8 I);cut (eta (klass b)(klass b) -> eta I b).
                                         ++++++ intro H8;apply MieT3 with (A:=klass b) in H8.
                                                * rewrite <-K8 in H8;apply singular_eq_eq_obj in K1;cut (set_eq (ι D)(klass a));[
                                                  intro;apply rewr_el_singleton_in_eta with (ϕ:=klass a);sfirstorder | scongruence unfold: set_eq ].
                                                 * sauto.
                                                 * sauto.
                                         ++++++ intro;assumption.
                                   +++++ intros I H8;cut (eta I (el (ι D)) /\ set_eq (klass a)(ι D));
                                                [ intro H9;apply rewl_el_singleton_in_eta in H9;specialize (K8 I);rewrite K8 in H9;cut (eta (klass b)(klass b) -> eta I (el (klass b)));
                                                        [ sauto use: MieT4 | sauto ] | hfcrush use: singleton_impl_in, In_indiv unfold: eta, incl ].
                         +++ auto.
           ---- assumption.
           ---- assumption.
      --- intro;assumption.
- apply MieT24 in K1;apply singular_eq_eq_obj in K1;apply MieT7 in H';apply MieT18 with (B:=B);split;assumption.
Qed.

Theorem SinAxI : forall P Q, eta P (pt Q) -> eta Q (neg (pt P)).
Proof.
hcrush use: negation, part, SinLI, MieT9.
Qed.

Lemma LejT4 : forall A B, eta A (pt B) -> Individual B.
Proof.
sfirstorder use: SinAxI unfold: eta.
Qed.

Lemma LejT5 : forall A B, eta A (pt B) -> ~(eta B (pt A)).
Proof.
hauto lq: on use: part, SinLI, SinXVIII, LejT4, LejT0.
Qed.

Lemma LejT6 : forall A, ~(eta A (pt A)).
Proof.
sauto use: LejT5.
Qed.

Lemma LejT8 : forall A B a, eta A (pt B) /\ eta B a -> eta A (pt (klass a)).
Proof.
intros A B a H;destruct H as [H1 H2];assert (H0:=H1);destruct H1 as [H1 H3];unfold eta;split.
- assumption.
- destruct H1 as [x H1];apply in_in_singleton with (A:=x);split.
  -- assumption.
  -- solve_op_in_goal pt;split.
     --- split.
         ---- apply N9.
         ---- split.
              ----- apply rewr_singleton_in_eta with (σ:=A);split;[ apply LejT12 with (B:=B);strivial use: part | sfirstorder ].
              ----- assert (H4:In (pt B) x).
                    ------ apply incl_in_singleton with (Φ:=A);split;assumption.
                    ------ solve_op_in_red_hyp H4 pt;destruct H5.
                           ------- destruct H4 as [[H4 [H5 H11]] H6];clear H6;intro H6. assert (H7:(set_eq (ι x)(klass a) <-> singular_eq (ι x)(klass a))).
                           + apply singular_eq_dec;split;[ apply N9 | apply LejT13 in H2;rewrite <-N1;assumption ].
                           + apply set_eq_sym in H6;rewrite H7 in H6;clear H7;apply MieT24' in H6;assert (H7: eta B (el A)).
                             ++ apply MieT3 with (a:=a);[hauto lq: on use: in_in_singleton, N11 unfold: eta | sauto ]. 
                             ++ assert (set_eq A B).
                                +++ apply SinLI;split;[ apply rewl_singleton_in_eta with (A:=x);solve_functor | assumption].
                                +++ assert (set_eq (ι x) B);[ scongruence use: set_eq_sym, part | sauto unfold: set_eq ].
                           ------- destruct H4;contradiction.
     --- auto.
Qed.

Theorem SinAxII : forall P Q R, eta P (pt Q) /\ eta Q (pt R) -> eta P (pt R).
Proof.
intros P Q R H;destruct H as [H1 H2];rewrite part in *;destruct H1, H2;split;[ sauto use: SinXXIII | hfcrush use: SinLI, MieT18 ].
Qed.

Lemma SinCXXII : forall P Q R, eta P (ext Q) /\ eta R (pt Q) -> eta P (ext R).
Proof.
qauto depth: 4 l: on use: Exterior, part, SinXXIII.
Qed.

Lemma SinXXXI : forall P, Individual P -> ~eta P (ext P).
Proof.
hfcrush use: SinII, Exterior.
Qed.

Lemma SinCXXII' : forall P Q R, eta P (ext Q) /\ eta R (el Q) -> eta P (ext R).
Proof.
intros P Q R [H1 H2];rewrite Exterior in H1;rewrite Exterior;destruct H1;split.
- assumption.
- destruct H0 as [H0 H1];split;[ sauto | qauto depth: 4 l: on use: SinXXIII ].
Qed.

Lemma SinXXXII : forall P Q, eta P (ext Q) -> eta Q (ext P).
Proof.
qauto depth: 4 l: on use: Exterior.
Qed.

Lemma SinIII : forall P Q, (exists R, eta R (pt P)) /\ eta Q (el P) -> exists X Y, eta X (el Q) /\ eta X (el Y) /\ eta Y (pt P).
Proof.
intros P Q[H1 H2];destruct H1 as [R H1];assert (H10:=H1); assert (H0:=H1);apply SinXVIII in H1;apply N2 in H0;apply MieT7 in H0.
assert (H7:=H2);assert (Individual Q).
- apply N2 in H7;rewrite N1 in H7;assumption.
- apply LejT0 with (B:=P) in H;rewrite H in H7;clear H;assert (exists u v, eta u (el P) /\ eta u (el v) /\ eta v (pt P));[
  firstorder | destruct H as [S [T [H3 [H4 H5]]]];destruct H7;[ hauto l: on use: MieT7, N41 | qauto depth: 4 l: on use: MieT18 unfold: el, pt ]].
Qed.

Lemma SinIX : forall P, (exists R, eta R (pt P)) -> eta P (klass (pt P)).
Proof.
intros P H;assert (H0:=H);destruct H as [R H];rewrite Klass;split;[ sauto use: LejT4 |
split;[ strivial use: part | intros Q H';assert ((exists R, eta R (pt P)) /\ eta Q (el P));[ sfirstorder | hecrush use: SinIII ]]]. 
Qed.

Lemma SinLXXXV : forall P Q, eta P (el Q) <-> (exists a, eta Q (klass a) /\ eta P a).
Proof.
qauto depth: 4 l: on use: SinVII, MieT9, MieT3 unfold: klass, el, incl, eta.
Qed.

Lemma SinV : forall P R, (forall S, eta S (el P) -> exists X, eta X (el S) /\ eta X (el R)) -> (forall Q, eta Q (el P) -> exists X Y, eta X (el Q) /\
                           eta Y (el R) /\ eta X (el Y) /\ eta Y (el P)).
Proof.
qauto depth: 4 l: on use: N1, SinXXIII, MieT7 unfold: el, eta.
Qed.


Lemma Collection : forall A a, eta A (coll a) <-> Individual A /\ forall Q, eta Q (el A) -> 
                                                  exists C D, eta C a /\ eta D (el C) /\ eta D (el Q) /\ eta C (el A).
Proof.
intros A a;split.
- intro H;solve_op_in_hyp H coll x;destruct H2.
  -- destruct H1 as [[H1 H2] H3];split.
     --- unfold Individual;exists x;assumption.
     --- intros B H4;assert (eta B (el (ι x))).
         ---- apply rewr_el_singleton_in_eta with (ϕ:=A);sfirstorder.
         ---- apply H2 in H5;destruct H5 as [C [D H5]];subst_set_eq_f H el x C;rewrite H6 in H5;exists C, D;assumption.
  -- destruct H1;contradiction.
- intros [H1 H2];unfold eta;split.
  -- assumption.
  -- destruct H1 as [x H1];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- solve_op_in_goal coll;split.
         ---- split;[ apply N9 |
              intros B H3;assert (eta B (el A));[ apply rewl_el_singleton_in_eta with (A:=x);sfirstorder |
              apply H2 in H0;destruct H0 as [C [D H0]];subst_set_eq_f H1 el x C;rewrite <-H4 in H0;exists C, D;assumption ]].
         ---- auto.
Qed.

Lemma SinVI : forall P Q a, eta P (klass a) /\ eta Q (el P) -> exists X Y, eta X (el Q) /\ eta Y a /\ eta X (el Y) /\ eta Y (el P).
Proof.
hfcrush use: Klass unfold: el, klass.
Qed.

Lemma SinXIV : forall P a, eta P (klass a) -> eta P (coll a).
Proof.
intros P a H;rewrite Collection;split.
- destruct H;assumption.
- intros Q H1;assert (eta P (klass a) /\ eta Q (el P));[ firstorder | hfcrush use: SinVI unfold: el, klass ].
Qed.

Lemma SinXV : forall P Q a, eta P (klass (coll a)) /\ eta Q (el P) -> exists X Y, eta X (el Q) /\ eta Y a /\ eta X (el Y).
Proof.
intros P Q a [H1 H0];rewrite Klass in H1;destruct H1 as [H1 [H2 H3]];apply H3 in H0;destruct H0 as [S [T [H5 [H6 H7]]]].
rewrite Collection in H5;destruct H5 as [H5 H8];apply H8 in H6;destruct H6 as [X [Y [K1 [K2 [K3 K4]]]]];exists Y, X. 
split;[ apply SinXXIII with (Q:=T);sfirstorder | split;auto ].
Qed.

Lemma SinXIII : forall P a, eta P a -> eta P (coll a).
Proof.
intros P a H;rewrite Collection;split.
- sfirstorder.
- strivial use: SinXIX, N41.
Qed.

Lemma SinXX : forall P a, eta P (klass a) -> (forall Q, eta Q a -> eta Q (el P)).
Proof.
sauto use: MieT3.
Qed.

Lemma SinXXI : forall P a, eta P (coll a) -> exists Q, eta Q a /\ eta Q (el P).
Proof.
hfcrush use: Collection, SinII unfold: coll, el, eta.
Qed.

Lemma SinXXIV : forall P a, eta P (klass (coll a)) -> eta P (klass a).
Proof.
intros P a H;assert (H10:=H);assert (H20:=H);rewrite Klass in H;rewrite Klass;destruct H;split.
- auto. 
- destruct H0 as [H1 H2];apply MieT2 in H10;destruct H10 as [Q H10];apply SinXXI in H10;destruct H10 as [R [H10 H4]];split;[
  intros S H5;apply SinXIII in H5;sauto | hecrush use: SinXV unfold: coll, el, klass ]. 
Qed.

Lemma SinXXV : forall P a, eta P (klass a) -> eta P (klass (coll a)).
Proof.
intros P a H; assert (H0:=H);apply SinXIV in H;apply klExistence in H;destruct H as [Q H];assert (H1:=H);apply SinXXIV in H;assert (Q ≡ P);
[ apply klUniq with (a:=a);sfirstorder | firstorder ]. 
Qed.

Lemma SinXXVbis : forall P a, eta P (klass a) <-> eta P (klass (coll a)).
Proof.
sauto use: SinXXV, SinXXIV.
Qed.

Lemma SinXXVI : forall P a, eta P (coll a) -> eta P (el (klass a)).
Proof.
intros P a H;assert (H0:=H);assert (H20:=H0);apply SinXXI in H;destruct H as [Q [H1 H2]];assert(H11:=H1);apply LejT13 in H11;rewrite N1 in H11;
apply klExistence in H1;destruct H1 as [R H1];assert (H10:=H1);destruct H0;clear H0;apply SinXXV in H1;rewrite Klass in H1.
destruct H1 as [H1 [H3 H4]]. assert (H15:=H10);apply MieT2 in H15;destruct H15 as [S H15]. apply H3 in H20;apply MieT24 in H10;assert (set_eq R (klass a) <-> R ≡ (klass a)).
- apply singular_eq_dec;split;assumption.
- rewrite <-H0 in H10;clear H0;destruct H1;subst_set_eq_f H0 el x P;assert (set_eq (ι x) (klass a)).
  -- apply set_eq_trans with (y:=R);assumption.
  -- subst_set_eq_f H5 el x P;rewrite H6 in H1;rewrite <-H1 in H20;assumption.
Qed.

Lemma SinXXVII : forall P R, Individual P /\ (forall S, eta S (el P) -> exists X, eta X (el S) /\ eta X (el R)) -> eta P (el R).
Proof.
intros P R [H1 H2];apply SinII in H1;assert (eta P (coll (el R))).
- rewrite Collection;split.
  -- destruct H1;assumption.
  -- intros Q H3;apply SinV with (Q:=Q) in H2;[ destruct H2 as [X [Y [K1 [K2 [K3 K4]]]]];exists Y, X;sauto | assumption ].
- assert (H3:=H);apply SinXXVI in H;apply SinXXI in H3;destruct H3 as [T [H3 H4]];apply SinX in H3;assert (H5:=H3);apply MieT24 in H3.
  destruct H5;clear H5;apply H2 in H1;destruct H1 as [U [H1 H5]];apply LejT13 in H5;destruct H5;clear H6;assert (set_eq R (klass (el R)) <-> R ≡ (klass (el R))).
  -- apply singular_eq_dec;split;assumption.
  -- rewrite <-H6 in H3;clear H6. destruct H0;subst_set_eq_f H0 el x P;assert (set_eq (ι x) (klass (el R))).
     --- apply set_eq_trans with (y:=R);assumption.
     --- subst_set_eq_f H7 el x P;rewrite H8 in H6;rewrite <-H6;assumption.
Qed.

Lemma SinXXVIII : forall P Q, eta P (SubColl Q) -> eta P (el Q).
Proof.
intros P Q H;unfold eta in H;destruct H as [H H'];unfold SubColl in H';unfold incl in H';assert (K0:=H);destruct H as [A H];specialize (H' A);cut (In P A).
- intro H1;apply H' in H1;clear H';unfold In in H1;unfold caract in H1;cut (True).
  -- intro H2;rewrite <-H1 in H2;clear H1;unfold IF_then_else in H2;destruct H2.
     --- rewrite and_true in H0. destruct H0 as [H0 H'];specialize (H' P);apply H';unfold eta;split.
          ---- assumption.
          ---- rewrite <-N1 in K0;apply MieT7 in K0;apply rewr_el_singleton_in_eta with (ϕ:=P);sfirstorder. 
     --- destruct H0;contradiction.
  -- auto.
- rewrite <-H;apply in_singleton.
Qed.

Lemma SinXXIX : forall P Q, eta P (el Q) -> eta P (SubColl Q).
Proof.
intros P Q H;unfold eta;split.
- destruct H;assumption.
- unfold SubColl;unfold incl;intros R H';simpl;unfold In;simpl;unfold IF_then_else;apply propositional_extensionality;split.
  -- intro;auto.
  -- intro;left;split.
     --- split;[ apply N9 |
         intros S H1;assert (H2:=H);destruct H as [H H3];destruct H as [A H];rewrite <-H in H';rewrite equiv_singleton in H';rewrite <-H' in H1;cut (eta S (el P));
         [ sauto use: SinXXIII | apply MieT18 with (B:=ι A);sfirstorder ]].
     --- auto.
Qed.

Lemma SinCXIV : forall P Q, eta P (el Q) <-> eta P (SubColl Q).
Proof.
sauto use: SinXXIX, SinXXVIII.
Qed.

Lemma SinCXV : forall P Q, eta P (el Q) -> ~(eta P (ext Q)).
Proof.
hcrush use: Exterior, N41.
Qed.

Lemma SinCXVII : forall P Q, eta P (pt Q) -> ~(eta P (ext Q)).
Proof.
hauto lq: on use: SinCXV, part.
Qed.

Lemma SinCXVI : forall P Q, Individual P /\ Individual Q /\ ~(exists X, eta X (el P) /\ eta X (el Q)) -> eta P (ext Q).
Proof.
hauto use: Exterior.
Qed. 

Lemma ext_el : forall P Q R, eta P (ext Q) /\ eta R (el P) -> eta R (ext Q).
Proof.
hfcrush use: SinXXXII, SinCXXII'.
Qed.

Lemma SinLVIII : forall P Q, (forall X, eta X (el P) /\ eta X (el Q)) -> eta P (el Q).
Proof.
sauto.
Qed.

Lemma SinCXXI : forall P Q R S, eta P (ext Q) /\ eta R (el Q) /\ eta S (el P) -> ~eta S (el R).
Proof.
intros P Q R S [H1 [H2 H3]];intro H4;assert (eta P (ext R)).
- apply SinCXXII' with (Q:=Q);sfirstorder.
- assert (eta S (ext R));[ apply ext_el with (P:=P);sfirstorder | apply SinCXV in H4;contradiction ].
Qed.

Lemma SinCXXIX : forall P Q, eta P (ext Q) <-> Individual P /\ Individual Q /\ ~(exists X, eta X (el P) /\ eta X (el Q)).
Proof.
intros P Q;split;[ intro H;rewrite Exterior in H;sauto | strivial use: SinCXVI ].
Qed.

Lemma SinCXXXI : forall P Q, eta P (ext Q) -> ~(exists X, eta X (pt P) /\ eta X (pt Q)).
Proof.
intros;rewrite SinCXXIX in H;hauto lq: on use: part.
Qed.

Lemma SinCXIX : forall P Q, Individual P /\ Individual Q /\ ~eta P (ext Q) -> set_eq P Q \/ eta P (pt Q) \/ eta Q (pt P) \/
                                                                                                            (exists X, eta X (el P) /\ eta X (el Q)).
Proof.
intros P Q [H1 [H2 H3]];classical_right;classical_right;classical_right;assert (~eta P (ext Q) -> ~(Individual P /\ Individual Q /\ ~(exists X, eta X (el P) /\ eta X (el Q)))).
- apply contra;strivial use: SinCXXIX.
- apply H5 in H3;clear H5;apply not_and_or in H3;destruct H3.
  -- contradiction.
  -- apply not_and_or in H3;destruct H3;[ contradiction | rewrite <-notnot in H3;assumption ].
Qed.


Lemma SinCXXXII : forall P Q, eta P (ext Q) <-> Individual P /\ Individual Q /\ ~set_eq P Q /\ ~eta P (pt Q) /\ ~eta Q (pt P) /\
                                                ~(exists X, eta X (pt P) /\ eta X (pt Q)).
Proof.
intros P Q;split.
- intro H;assert (H0:=H);rewrite SinCXXIX in H0;destruct H0 as [H0 [H1 H2]];split.
  -- assumption.
  -- split.
     --- assumption.
     --- split.
         ---- intro H3;apply H2;exists P;split;[ apply SinII in H0;assumption | hfcrush use: LejT0, SinII ].
         ---- split.
              ----- intro H3;sauto use: SinCXVII.
              ----- split;[ hauto lq: on use: N1, part, MieT7 | intro H3;apply H2;destruct H3 as [R [H3 H4]];exists R;strivial use: Part ].
- intros [H1 [H2 [H3 [H4 [H5 H6]]]]];rewrite Exterior;split.
  -- assumption.
  -- split.
     --- assumption.
     --- intro H7;apply H6;clear H6;destruct H7 as [R [H7 H8]];exists R;split.
         ---- rewrite part;split.
              ----- assumption.
              ----- intro H0;assert (eta P (el Q));[ apply eq_indiv_in_eta with (A:=R);split;[ assumption | apply set_eq_sym;assumption ] | 
                    apply LejT0 with (B:=Q) in H1;rewrite H1 in H;destruct H;[ contradiction | apply set_eq_sym in H;contradiction ]].
         ---- rewrite part;split.
              ----- assumption.
              ----- intro H0;assert (eta Q (el P));[ apply eq_indiv_in_eta with (A:=R);split;[ assumption | apply set_eq_sym;assumption ] | 
                    apply LejT0 with (B:=P) in H2;rewrite H2 in H;destruct H;contradiction ].
Qed.

Lemma SinCXXXVI : forall P Q R S T, Individual R /\ eta P (klass (Q ∪ R)) /\ eta S (el P) /\ eta S (ext Q) /\ eta T (el S) -> exists X, eta X (el T) /\ eta X (el R).
Proof.
intros P Q R S T [H1 [H2 [H3 [H4 H5]]]];assert (eta T (el P)).
- apply SinXXIII with (Q:=S);split;assumption.
- assert (K10:=H);assert (K0:=H4);apply SinXXXII in H4;assert (K11:=H4);destruct H4;rewrite Klass in H2;destruct H2 as [H2 [H6 H7]];apply H7 in H;destruct H as [W [U [K1 [K2 K3]]]]. rewrite OntoT157 in K1.
  assert (eta U (el S)).
  -- apply SinXXIII with (Q:=T);split;assumption.
  -- rewrite Exterior in K0;destruct K0 as [K0 [K5 K6]];apply not_ex_all_not with (n:=U) in K6;apply not_and_or in K6;destruct K6.
     --- clear H4;assert (~eta W Q);[assert (eta Q (ext U));[ apply SinCXXII' with (Q:=S);split;assumption | intro H9;assert (eta W (ext U));[ 
         apply OntoT7 with (B:=Q);sfirstorder | apply SinCXV in K2;apply SinXXXII in H10;contradiction ]] |
         destruct K1;[ contradiction |
         exists U;split;[  assumption |
         assert (eta R W);[ apply OntoT6 with (a:=R);split;[ assumption | rewrite <-N1 in H1;assumption ] |
         assert (W ≡ R);[ unfold singular_eq;split;assumption |
         destruct H9;assert (Individual W /\ Individual R);[ split;assumption |
         apply singular_eq_dec in H13;rewrite <-H13 in H11;clear H13;apply MieT18 with (B:=W);split;assumption ]]]]]].
    --- contradiction.
Qed.

Lemma SinCXLII : forall P Q R S, Individual R /\ eta P (klass (Q ∪ R)) /\ eta S (el P) /\ eta S (ext Q) -> eta S (el R).
Proof.
intros P Q R S [H1 [H2 [H3 H4]]];apply SinXXVII;split.
- sfirstorder.
- intros T H5;apply (SinCXXXVI P Q R S T);sfirstorder.
Qed.

Lemma SinXXX : forall P Q, eta P (pt Q) -> eta P (SubColl Q).
Proof.
hfcrush use: SinCXIV, part.
Qed.

Lemma SinXXII : forall P Q, eta P (pt Q) -> ~(forall R a, (exists S, eta S (coll a) /\ eta R (el S)) -> eta R a).
Proof. 
intros P Q H;assert (H1:=H);apply LejT4 in H;rewrite <-N1 in H;assert (H2:=H);apply SinXIII in H;assert (H3:=H1);apply SinXVIII in H3;assert (~(eta Q (pt Q)));[
apply LejT6 | assert (~eta P Q);[ hfcrush use: Part, OntoT21 unfold: pt | intro H5;specialize (H5 P Q);apply contra in H5;[ hauto lq: on | assumption ]]].
Qed.


(** Theorems about complements of objects **)

Lemma SinXXXIII : forall P Q R :N, eta P (relCompl Q R) -> eta Q (el Q).
Proof.
qauto use: relatComp, SinII unfold: eta.
Qed.

Lemma SinXXXIV : forall P Q R S:N, eta P (relCompl Q R) /\ eta S (el P) -> exists X Y, eta X (el S) /\ 
                                                          eta X (el Y) /\ eta Y (el R) /\ eta Y (ext Q).
Proof.
intros P Q R S [H1 H2];rewrite relatComp in H1;destruct H1 as [H1 [H3 H4]];assert (H5:=H4);rewrite Klass in H4;destruct H4 as [H4 [H6 H7]].
apply MieT2 in H5;destruct H5 as [Y H5];rewrite OntoT134 in H5;apply H7 in H2;destruct H2 as [C [D [K1 [K2 K3]]]].
rewrite OntoT134 in K1;exists D, C;split;sauto.
Qed.

Lemma SinXXXV : forall P Q R S:N, eta P (relCompl Q R) /\ eta S (el P) -> exists X, eta X (el S) /\ eta X (el R).
Proof.
intros P Q R S H;apply SinXXXIV in H;destruct H as [A [B [K1 [K2 [K3 K4]]]]];exists A;split;[ assumption | apply SinXXIII with (Q:=B);split;assumption ].
Qed.

Lemma SinXXXVI : forall P Q R :N, eta P (relCompl Q R) -> eta P (ext Q).
Proof.
intros P Q R H;assert (H0:=H);apply SinXXXIII in H0;rewrite Exterior;split.
- destruct H;assumption.
- split.
  -- destruct H0;assumption.
  -- intro H1;destruct H1 as [S [H1 H2]];assert (eta P (relCompl Q R) /\ eta S (el P)).
     --- split;assumption.
     --- apply SinXXXIV in H3;destruct H3 as [C [D [K1 [K2 [K3 K4]]]]];rewrite Exterior in K4;destruct K4 as [K4 [K5 K6]].
         apply K6;exists C;split;[ apply SinXXIII with (Q:=S);split;assumption | assumption ].
Qed.

Lemma SinXXXVII : forall P R :N, Individual P -> ~eta P (relCompl P R).
Proof.
intros;intro H1;apply SinXXXVI in H1;apply SinXXXI in H;contradiction.
Qed.

Lemma SinXXXVIII : forall P Q R S :N, eta P (relCompl Q R) /\ eta S (relCompl Q R) -> P ≡ S.
Proof.
intros P Q R S [H1 H2];rewrite relatComp in *;destruct H1 as [H1 [H3 H4]], H2 as [H2 [H5 H6]];apply klUniq with (a:=el R ∩ ext Q);sfirstorder.
Qed.

Lemma SinXXXIX : forall P Q R :N, eta P (relCompl Q R) -> eta P (el R).
Proof.
intros P Q R H;apply SinXXVII;split;[ sfirstorder |
intros S H';assert (eta P (relCompl Q R) /\ eta S (el P));[ sfirstorder | sauto use: SinXXXV unfold: el, relCompl ]].
Qed.

Lemma SinXL : forall P Q R S :N, eta P (relCompl Q R) /\ eta S (el R) /\ ~eta S (el Q) -> ~eta S (ext P).
Proof.
intros P Q R S [H1 [H2 H3]];assert (H0:=H1);rewrite relatComp in H1;destruct H1 as [H1 [H5 H4]];clear H1 H5;apply SinXXXIII in H0.
intro H5;apply H3;apply SinXXVII;split.
- destruct H2;assumption.
- intro T;apply contra1;intro H6;intro H8;assert (H9:eta T (el R)).
  -- apply SinXXIII with (Q:=S);split;assumption.
  -- assert (eta T (ext Q)).
     --- rewrite Exterior;split;[ sauto |
         split;[ destruct H0;assumption | intro H10;apply H6;destruct H10 as [X [H10 H11]];exists X;split;assumption ]].
     --- rewrite Klass in H4;destruct H4 as [K1 [K3 K4]];specialize (K3 T);rewrite OntoT134 in K3;assert (eta T (el P)).
         ---- apply K3;split;assumption.
         ---- rewrite Exterior in H5;destruct H5 as [H5 [K5 K6]];apply K6;exists T;split;assumption.
Qed.

Lemma SinXLI : forall P Q R S, eta P (relCompl Q R) /\ eta S (el R) -> exists T U, eta T (el S) /\ eta U (Q ∪ P) /\ eta T (el U).
Proof.
intros P Q R S [H1 H2];assert ((eta P (relCompl Q R) /\ eta S (el R) /\ ~eta S (el Q)) -> ~eta S (ext P)).
- apply SinXL.
- apply imply_to_or in H;destruct H.
  -- apply not_and_or in H;destruct H.
     --- contradiction.
     --- apply not_and_or in H;destruct H.
         ---- contradiction.
         ---- rewrite <-notnot in H;rewrite relatComp in H1;hfcrush use: MieT7, N41, OntoT157.
  -- rewrite Exterior in H;apply not_and_or in H;destruct H.
     --- destruct H2;contradiction.
     --- apply not_and_or in H;destruct H;[ destruct H1;contradiction |
         rewrite <-notnot in H;destruct H as [T [H3 H4]];exists T, P;qauto depth: 4 l: on use: N41, OntoT157 ].
Qed.


(** a provable weak supplementation axiom in Lesniewski's mereology **)

Lemma SinXLII : forall P Q, eta P (pt Q) -> exists R, eta R (relCompl P Q).
Proof.
intros P Q H1;assert (H2:=H1);assert (H3:=H1);apply SinXXX in H1;apply LejT5 in H2;assert (H4:=H3);assert (~(Q ≡ P)).
- hauto lq: on use: singular_eq_eq_obj, part.
- assert (H15:=H1);assert (~(eta Q (el P))).
  -- rewrite LejT0;[ apply and_not_or;split;[ assumption | intro;apply H;assert (Individual P /\ Individual Q);[ split;[ 
     destruct H1 | apply LejT4 in H4 ];assumption | apply singular_eq_dec in H5;rewrite H5 in H0;apply singular_eq_sym;assumption ]]
     | rewrite <-SinCXIV in H1;apply MieT9 in H1;assumption ].
  -- destruct H3;apply SinII in H3;clear H5;assert (~eta Q (el P) -> ~(Individual Q /\ (forall S, eta S (el Q) -> exists X, eta X (el S) /\ eta X (el P)))).
      --- apply contra;apply SinXXVII.
      --- apply H5 in H0;clear H5;apply not_and_or in H0;destruct H0.
          + apply LejT4 in H4;contradiction.
          + apply not_all_ex_not in H0;destruct H0 as [S H0];assert (H10:=H0);apply not_imply_elim in H10;apply not_imply_elim2 in H0;assert (eta S (ext P)).
            ++ rewrite Exterior;split;[ destruct H10;assumption |
               split;[ destruct H4;assumption | intro;apply H0;destruct H5 as [C [H5 H6]];exists C;split;assumption ]].
            ++ assert (eta S ((el Q) ∩ (ext P)));[ apply OntoT134;split;assumption |
               apply klExistence in H6;destruct H6 as [R H6];exists R;rewrite relatComp;split;[ destruct H6;assumption | split;assumption ]].
Qed.

Lemma SinXLIII : forall P Q R, eta P (relCompl Q R) -> eta P (pt R).
Proof.
intros P Q R H;assert (H0:=H);apply SinXXXIX in H0;assert (H1:=H);apply SinXXXVI in H1;rewrite relatComp in H.
destruct H as [H2 [H3 H4]];rewrite <-SinCXIV in H3;rewrite part;split.
- auto.
- intro;assert (eta Q (el P));[ sauto use: MieT18 | apply SinCXV in H5;apply SinXXXII in H1;contradiction ].
Qed.

Lemma SinXLIV : forall P Q, Individual P -> ~eta P (relCompl Q P).
Proof.
intros P Q H;assert (~eta P (pt P) -> ~eta P (relCompl Q P));[ sauto use: SinXLIII | sauto use: LejT6 ].
Qed.

Lemma SinXLV : forall P Q R, eta P (relCompl Q R) -> eta Q (relCompl P R).
Proof.
intros;assert (H0:=H);assert (H9:=H0);assert (H11:=H0);apply SinXLIII in H;assert (H10:=H);apply SinXXX in H;apply SinXXVIII in H;apply SinXXXVI in H0;rewrite relatComp;split.
- apply SinXXXII in H0;destruct H0;assumption.
- split.
  -- apply SinXXX;assumption.
  -- rewrite Klass;rewrite relatComp in H9. destruct H9 as [H1 [H2 H3]]. apply SinII in H1;split.
     --- destruct H2;assumption.
     --- split.
         ---- intros S H4;rewrite OntoT134 in H4;destruct H4;clear H2. assert (eta S (ext P) -> ~(eta P (relCompl Q R) /\ eta S (el R) /\ ~eta S (el Q))).
              ----- apply Contra;rewrite <-notnot;apply SinXL.
              ----- apply H2 in H5;clear H2;apply not_and_or in H5;destruct H5.
                    + contradiction.
                    + apply not_and_or in H2;destruct H2;[ contradiction | rewrite <-notnot in H2;assumption ].
         ---- intros S H4;exists Q, S;hfcrush use: SinCXIV, SinXXXII, SinII, OntoT134 unfold: SubColl, eta, n_conjunction.
Qed.

Lemma SinXLVI : forall P Q R, eta P (relCompl Q R) -> eta Q (pt R).
Proof.
hcrush use: SinXLIII, SinXLV.
Qed.

Lemma SinXLVIII : forall P Q R, eta P (relCompl Q R) -> eta R (klass (P ∪ Q)).
Proof.
intros P Q R H1;assert (H0:=H1);apply SinXLVI in H0;apply part in H0;destruct H0;rewrite Klass;split.
- apply MieT9 in H;assumption.
- split.
  -- intros S H2;rewrite OntoT157 in H2;destruct H2;[ apply OntoT7 with (B:=P);split;[ assumption | apply SinXXXIX with (Q:=Q);assumption ]| 
     apply OntoT7 with (B:=Q);split;assumption ].
  -- intros S H2. assert (eta P (relCompl Q R) /\ eta S (el R));[ sfirstorder |
     apply SinXLI in H3;destruct H3 as [T [U [H3 [H4 H5]]]];exists U, T;strivial use: OntoT159 ].
Qed.

Lemma el_to_ext : forall P Q R, eta P (el Q) /\ eta Q (ext R) -> eta P (ext R).
Proof.
hfcrush use: ext_el.
Qed.

Lemma coll_eq : forall C a b, eta C (coll a) /\ set_eq a b -> eta C (coll b).
Proof.
hauto l: on use: N22, Collection.
Qed.


(** Theorems about binary sums **)

Definition plus (Q R :N) : N := 
      Caract (fun P:object => IF_then_else (eta Q (ext R) /\ eta (ι P)(klass (Q ∪ R))) True False).

Lemma plus_r : forall P Q R, eta P (plus Q R) <-> (eta Q (ext R) /\ eta P (klass (Q ∪ R))).
Proof.
intros;split.
- intro. unfold eta in H;assert (H19:=H);destruct H as [[x H] H20];assert (H21:set_eq (ι x) P /\ incl P (plus Q R)).
  -- split;assumption.
  -- apply incl_in_singleton in H21;unfold In in H21;unfold plus in H21;unfold IF_then_else in H21;simpl in H21;assert (H1:True).
     --- auto.
     --- rewrite <-H21 in H1;clear H21;destruct H1.
         ---- destruct H0 as [[H1 H2 ] H0];split;[ assumption |
              qauto use: incl_equivl unfold: ι, eta, n_disjunction ].
         ---- destruct H0;contradiction.
- intros [H1 H2];unfold eta;split.
  -- destruct H2;assumption.
  -- destruct H2 as [[x H2] H3];apply in_in_singleton with (A:=x);split.
     --- assumption.
     --- unfold In;unfold plus;unfold IF_then_else;simpl;apply propositional_extensionality;split.
         ---- intro;auto.
         ---- intro;left;split;[split;[ assumption |
                    hauto use: N9 unfold: eta, incl, set_eq ] | auto ].
Qed.

Lemma SinLV : forall P a, Individual P /\ (forall Q, eta Q a -> eta Q (el P)) /\ 
                            (forall Q, eta Q (el P) -> exists D E, eta D a /\ eta E (el D) /\ eta E (el Q)) -> eta P (klass a).
Proof.
intros P a [H1 [H2 H3]];rewrite Klass;split;sfirstorder.
Qed.

Lemma SinLVII : forall P a, eta P (klass a) <-> (Individual P /\ (forall Q, eta Q a -> eta Q (el P)) /\ (forall Q, eta Q (el P) -> 
                                                 exists D E, eta D a /\ eta E (el D) /\ eta E (el Q))).
Proof.
intros P a;split;[ intro H;rewrite Klass in H;destruct H as [H0 [H2 H3]];split;firstorder | hcrush use: SinII, Klass ].
Qed.

Lemma SinLX : forall P a, (forall R, eta R a /\ eta R (el P)) /\ (forall Q, eta Q (el P) -> exists X Y, eta X (el Q) /\ eta Y a /\ eta X (el Y)) -> eta P (klass a).
Proof.
intros P a [H1 H2];rewrite Klass;split;[ strivial unfold: eta | hfcrush use: SinII unfold: eta ].
Qed.

Lemma SinLXII : forall P a b, eta P (klass a) /\ (forall Q, eta Q a <-> eta Q b) -> eta P (klass b).
Proof.
hfcrush use: set_eq_incl, weak_to_incl, MieT16 unfold: weakInclusion.
Qed.

Lemma SinLXIII : forall P Q R a, eta P (klass a) /\ eta Q (el R) /\ eta Q (el P) -> exists X Y, eta Y a /\ eta X (el R) /\ eta X (el Y).
Proof.
qauto depth: 4 l: on use: SinXXIII, MieT4.
Qed.

Lemma SinLXIV : forall P Q R a b, eta P (klass a) /\ eta Q (klass b) /\ eta R (klass (P ∪ Q)) -> (forall S, eta S (a ∪ b) -> eta S (el R)).
Proof.
intros P Q R a b [H1 [H2 H3]];intros S H4;assert (L1:=H1);assert (L2:=H3);apply SinLVII in H1;apply SinLVII in H2;destruct H1 as [H1 [K1 K2]];destruct H2 as [H2 [K3 K4]].
rewrite OntoT157 in H4;specialize (K1 S);specialize (K3 S);assert (eta S (el P) \/ eta S (el Q)).
- destruct H4;[ left;apply K1;assumption | right;apply K3;assumption ].
- apply SinLVII in L2;destruct L2 as [K5 [K6 K7]];assert (K0:=K6);specialize (K6 P);assert (eta P (el R)).
  -- hfcrush use: N1, D8.
  -- specialize (K0 Q);assert (eta Q (el R));[ hfcrush use: N1, D8 |
     destruct H;[ apply SinXXIII with (Q:=P) | apply SinXXIII with (Q:=Q) ];sfirstorder ].
Qed.

Lemma SinLXV : forall P Q R a b, eta P (klass a) /\ eta Q (klass b) /\ eta R (klass (P ∪ Q)) -> (forall S, eta S (el R) -> exists X Y, eta Y (a ∪ b) /\ eta X (el S) /\ eta X (el Y)).
Proof.
intros P Q R a b [H1 [H2 H3]];intros S H4;rewrite Klass in H3;destruct H3 as [H3 [H6 H7]];apply H7 in H4;clear H7;destruct H4 as [U [T [H4 [H7 H8]]]].
rewrite OntoT157 in H4;assert (eta U (klass a) \/ eta U (klass b)).
- destruct H4;[ classical_left;apply OntoT7 with (B:=P);sfirstorder | classical_right;apply OntoT7 with (B:=Q);sfirstorder ].
- destruct H.
  -- assert (exists X Y, eta Y a /\ eta X (el S) /\ eta X (el Y)).
     --- apply SinLXIII with (P:=U)(Q:=T);split;sfirstorder. 
     --- destruct H0 as [X [Y [K1 [K2 K3]]]];exists X, Y;split;[ rewrite OntoT157;classical_left;auto | sfirstorder ].
  -- assert (exists X Y, eta Y b /\ eta X (el S) /\ eta X (el Y)).
     --- apply SinLXIII with (P:=U)(Q:=T);split;[ assumption | split;assumption ].
     --- destruct H0 as [X [Y [K1 [K2 K3]]]];exists X, Y;split;[ rewrite OntoT157;classical_right;auto | sfirstorder ].
Qed. 

Lemma SinLXVI : forall P Q R a b, eta P (klass a) /\ eta Q (klass b) /\ eta R (klass (P ∪ Q)) -> eta R (klass (a ∪ b)).
Proof.
intros P Q R a b [H1 [H2 H3]];assert (H0:=H3);apply MieT2 in H3;destruct H3 as [S H3];assert (forall S, eta S (a ∪ b) -> eta S (el R)).
- apply SinLXIV with (P :=P)(Q :=Q)(a :=a)(b :=b);sfirstorder. 
- assert (forall S, eta S (el R) -> exists X Y, eta Y (a ∪ b) /\ eta X (el S) /\ eta X (el Y)).
  -- apply SinLXV with (P:=P)(Q:=Q);sfirstorder.
  -- apply SinLV;hauto unfold: n_disjunction, el, eta.
Qed. 

Lemma SinLXVIII : forall P Q a b, eta P (klass a) /\ (forall R, eta R (klass a) -> eta R (klass b)) /\ eta Q (klass b) -> eta Q (klass a).
Proof.
intros P Q a b [H1 [H2 H3]];assert (H10:=H1);apply H2 in H1;assert (P ≡ Q).
- apply klUniq with (a:=b);sfirstorder.
- assert (Individual P /\ Individual Q);sfirstorder.
Qed.

Lemma SinLXXV : forall P Q R a b, eta P (klass a) /\ eta Q (klass b) /\ eta R (klass (a ∪ b)) -> eta R (klass (P ∪ Q)).
Proof.
intros P Q R a b [H1 [H2 H3]];assert (exists S, eta S (P ∪ Q)).
- qauto depth: 4 l: on use: OntoT157, MieT1. 
- destruct H as [S H4];apply klExistence in H4;destruct H4 as [T H4];assert (eta T (klass (a ∪ b)));[
  apply SinLXVI with (P:=P)(Q:=Q);sfirstorder | hauto lq: on use: OntoT7, OntoT6, N1, MieT24 unfold: klass, n_disjunction, eta, singular_eq ].
Qed.

Lemma SinLXXVII : forall P Q a, (forall R S, eta R (coll a) /\ eta S (coll a) -> eta R S) /\ eta P a /\ eta Q a -> eta P Q.
Proof.
sauto use: SinXIII.
Qed.

Lemma SinLXXX : forall P a, eta P (coll a) /\ (forall Q, eta Q a -> eta Q (el P)) -> eta P (klass a).
Proof.
intros P a [H1 H2];rewrite Collection in H1;destruct H1;apply SinLV;split;[ sfirstorder | fcrush ].
Qed.

Lemma SinLXXXI : forall P a, eta P (coll a) -> (forall Q, eta Q a -> eta Q (el P)) -> eta P (klass a).
Proof.
sauto use: SinLXXX.
Qed.

Lemma SinLXXXII : forall P a, eta P (klass a) <-> (eta P (coll a) /\ (forall Q, eta Q a -> eta Q (el P))).
Proof.
strivial use: MieT3, SinXIV, SinLXXX.
Qed.

Lemma SinLXXXVI : forall P Q a, eta Q (klass a) /\ eta P a -> eta P (pt Q) \/ eta P Q .
Proof.
intros P Q a [H1 H2];assert (Individual P /\ Individual Q).
- destruct H1, H2;split;assumption.
- apply singular_eq_dec in H;assert (eta P Q /\ Individual Q -> P ≡ Q).
  -- intros [H0 H3];unfold singular_eq;split;[ assumption | strivial use: OntoT287 unfold: singular_eq ].
  -- assert (H10:=H2);apply SinLXXXII in H1;destruct H1 as [H1 H3];apply H3 in H2;destruct H10;apply LejT0 with (B:=Q) in H4;rewrite H4 in H2.
     destruct H2;[ classical_left;assumption | classical_right;apply set_eq_sym in H2;rewrite H in H2;unfold singular_eq in H2;destruct H2;assumption ].
Qed.

Lemma SinXCII : forall P S a, eta P (coll a) /\ (forall Q R, eta Q a /\ eta R a -> eta Q R) /\ eta S a -> eta S (el P).
Proof.
intros P S a [H1 [H2 H3]];apply SinXXI in H1;destruct H1 as [R [H0 H1]];specialize (H2 S R);assert (eta S R);sfirstorder.
Qed.

Lemma SinXCIV : forall P a, eta P (coll a) /\ (forall Q R, eta Q a /\ eta R a -> eta Q R) -> eta P (klass a).
Proof.
hauto lq: on use: SinLXXXI, SinXCII unfold: coll, klass, el.
Qed.

Lemma SinXCVIII : forall R S a, (forall P Q, eta P a /\ eta Q a -> eta P Q) /\ eta R (coll a) /\ eta S (coll a) -> eta R S.
Proof.
intros R S a [H1 [H2 H3]];assert (eta R (klass a) /\ eta S (klass a) -> eta R S).
- hauto lq: on use: klUniq unfold: klass, singular_eq. 
- hauto use: SinXCIV unfold: coll, klass. 
Qed.

Lemma SinC : forall a, (forall P Q, eta P a /\ eta Q a -> eta P Q) <-> (forall R S, eta R (coll a) /\ eta S (coll a) -> eta R S).
Proof.
hfcrush use: SinXIII, SinXCVIII.
Qed.

Lemma SinCXXXV : forall P Q a, eta P (klass a) /\ Individual Q /\ ~eta Q (ext P) -> exists R, eta R a /\ ~eta Q (ext R).
Proof.
intros P Q a [H1 [H2 H3]]. 
assert ( eta Q (ext P) <-> Individual Q /\ Individual P /\ ~(exists X, eta X (el Q) /\ eta X (el P))).
- apply SinCXXIX.
- destruct H;rewrite Contra in H, H0. 
  assert (¬ eta Q (ext P) <-> ¬ (Individual Q ∧ Individual P ∧ ¬ (∃ X : N, eta X (el Q) ∧ eta X (el P)))).
  -- split;assumption.
  -- clear H H0;rewrite H4 in H3;clear H4;apply not_and_or in H3;destruct H3.
     --- contradiction.
     --- apply not_and_or in H;destruct H.
         ---- destruct H1;contradiction.
         ---- rewrite <-notnot in H;destruct H as [R [H3 H4]];assert (exists S T, eta T a /\ eta S (el Q) /\ eta S (el T)).
              ----- apply SinLXIII with (P:=P)(Q:=R);split;[ assumption | split;assumption ].
              ----- destruct H as [S [T [H5 [H6 H7]]]];exists T;split;[ assumption |
                    intro H0;rewrite Exterior in H0;destruct H0 as [K1 [K2 K3]];apply K3;clear K3;exists S;split;assumption ].
Qed.

Lemma SinCXXXVII : forall P Q R a, eta P (klass a) /\ eta Q (ext P) /\ eta R a -> eta Q (ext R).
Proof.
intros P Q R a [H1 [H2 H3]];apply SinCXXII' with (Q:=P);split.
- assumption.
- assert (H4:=H3);apply MieT22 in H3;assert (H5:=H1);apply MieT24 in H5;assert (set_eq P (klass a) <-> P ≡ klass a);[
  sauto use: singular_eq_eq_obj unfold: klass | sauto use: MieT3 ]. 
Qed.

Lemma SinCXXXVIII : forall P Q a, eta P (klass a) /\ (forall R, eta R a -> eta Q (ext R)) -> eta Q (ext P).
Proof.
intros P Q a [H1 H2];assert (H0:=H1);assert (H10:=H2);apply MieT2 in H0;destruct H0 as [R H0];assert (H4:=H0);apply H2 in H0;destruct H0.
specialize (H2 R);apply imply_to_or in H2;clear H0;destruct H2.
- contradiction.
- assert (~(exists R, eta R a /\ ~eta Q (ext R)) -> ~(eta P (klass a) /\ Individual Q /\ ~eta Q (ext P))).
  -- apply contra;apply SinCXXXV.
  -- assert ( ¬ (∃ R : N, eta R a ∧ ¬ eta Q (ext R))).
     --- intro;destruct H3 as [S H3];specialize (H10 S);apply imply_to_or in H10;assert (eta Q (ext S) <-> ~~eta Q (ext S)).
         ---- apply notnot.
         ---- rewrite H5 in H10;clear H5;apply or_not_and in H10;contradiction.
     --- apply H2 in H3;clear H2. apply not_and_or in H3;destruct H3;[ contradiction |
         apply not_and_or in H2;destruct H2;[ contradiction | rewrite notnot;assumption ]].
Qed.

Lemma SinCXLI : forall P R, Individual P /\ (forall Q, ~eta Q (ext P)) /\ Individual R -> eta R (el P).
Proof.
intros P R [H1 [H2 H3]];assert (H10:=H2);assert (~eta R (ext P) -> ~(Individual R /\ Individual P /\ ~(exists X, eta X (el R) /\ eta X (el P)))).
- apply contra;intros;apply SinCXVI;destruct H as [H4 [H5 H6]];split;[ auto | sfirstorder ].
- specialize (H2 R);apply H in H2;clear H;apply not_and_or in H2;destruct H2.
  -- contradiction.
  -- apply not_and_or in H;destruct H.
     --- contradiction.
     --- rewrite <-notnot in H;apply SinXXVII;split;[ assumption |
         intros S H4;specialize (H10 S);rewrite SinCXXIX in H10;apply not_and_or in H10;destruct H10;[ destruct H4;contradiction |
         apply not_and_or in H0;destruct H0;[ contradiction | rewrite <-notnot in H0;assumption ]]].
Qed.

Lemma SinCXLIII :forall P, Individual P /\ (forall Q, ~eta Q (ext P)) -> eta P (klass P).
Proof.
sfirstorder use: N1, MieT12.
Qed.

Lemma SinCXXXIX : forall a P Q, eta P (klass a) -> (eta Q (ext P) <-> (forall R, eta R a -> eta Q (ext R))).
Proof.
hauto depth: 2 lq: on exh: on use: SinCXXXVII, SinCXXXVIII.
Qed.

Lemma SinCXLV : forall P Q R, eta P (relCompl Q R) <-> (eta Q (el R) /\ eta P (klass (el R ∩ ext Q))).
Proof.
intros;split;[ hauto lq: on use: SinXLVI, part, relatComp | hfcrush use: SinCXIV, relatComp unfold: klass, ext, el, SubColl, relCompl, n_conjunction, eta ].
Qed.

Lemma SinCXLVII : forall P Q, ~eta P (plus Q Q).
Proof.
hauto lq: on use: plus_r, SinXXXI, Exterior.
Qed.

Lemma SinCXLVIII : forall P Q R, eta P (plus Q R) -> eta R (ext Q).
Proof.
hauto lq: on use: SinXXXII, plus_r.
Qed.

Lemma SinCIL : forall P Q R S T, eta P (plus Q R) /\ eta S (Q ∪ R) /\ eta T (Q ∪ R) -> set_eq S T \/ eta S (ext T).
Proof.
intros P Q R S T [H1 [H2 H3]];rewrite D8 in *;rewrite plus_r in H1;destruct H1 as [K1 K2], H2 as [H2 H4], H3 as [H3 H5].
destruct H4.
- destruct H5.
  -- apply OntoT2' with (C:=S)(D:=T) in K1;[ classical_left;assert (set_eq S T <-> S ≡ T);
     [ sauto use: singular_eq_eq_obj | firstorder ] | sfirstorder ].
  -- classical_right;assert (eta S (ext R));[ firstorder |
     apply SinXXXII;apply SinXXXII in H4;apply OntoT7 with (B:=R);sfirstorder ].
- destruct H5.
  -- classical_right;assert (eta T (ext R)).
     --- firstorder. 
     --- apply SinXXXII in H4;apply OntoT7 with (B:=R);split;assumption.
  -- classical_left;apply SinXXXII in K1;apply OntoT2' with (C:=S)(D:=T) in K1.
     --- assert (set_eq S T <-> S ≡ T);[ sauto use: singular_eq_eq_obj | sfirstorder ].
     --- auto.
Qed.

Lemma SinCLI : forall P Q R S, eta P (plus Q R) /\ eta S (ext P) -> eta S (ext Q).
Proof.
intros P Q R S [H1 H2];rewrite plus_r in H1;destruct H1 as [H1 H3];apply SinCXXII' with (Q:=P);split;[ auto |
hauto use: MieT3, OntoT157, N1 unfold: el, eta, n_disjunction, ext, klass ].
Qed.

Lemma SinCLII : forall P Q R S, eta P (plus Q R) /\ eta S (ext Q) /\ eta S (ext R) -> eta S (ext P).
Proof.
intros P Q R S [H1 [K2 K3]];rewrite plus_r in H1;destruct H1 as [H1 H3];apply SinXXXII;apply SinCXXII' with (Q:=S);split.
- apply SinXXXII;apply SinCXXXVIII with (a:=(Q ∪ R));split.
  -- assumption.
  -- intros T H7;rewrite D8 in H7;destruct H7;destruct H0.
     --- apply SinXXXII;apply SinXXXII in K2;apply OntoT7 with (B:=Q);split;assumption.
     --- apply SinXXXII;apply SinXXXII in K3;apply OntoT7 with (B:=R);split;assumption.
- apply SinXIX in K2;assumption.
Qed.

Lemma SinCLIII : forall P Q R S, eta P (plus Q R) /\ eta S (plus Q R) -> P ≡ S.
Proof.
hauto depth: 2 lq: on exh: on use: N5, MieT24, plus_r, OntoT287 unfold: singular_eq, klass, n_disjunction, plus, eta.
Qed.

Lemma SinCLIV : forall P S T a, (forall Q R, eta Q a /\ eta R (klass (a ∩ (neg Q))) -> eta P (plus Q R)) /\ eta S a /\ eta T a -> ~(eta S T) -> eta S (ext T).
Proof.
intros P S T a [H1 [H2 H3]] H4;assert (Individual S /\ ~eta S T).
- split;[ destruct H2;assumption | assumption ].
- rewrite <-negation in H;assert (eta T (neg S)).
  -- apply OntoT30 with (a:=a);split;assumption.
  -- assert (eta T (a ∩ (neg S)));[ rewrite OntoT134;split;assumption |
     apply klExistence in H5;destruct H5 as [U H5];assert (eta P (plus S U));[ apply H1;split;assumption |
     rewrite plus_r in H6;destruct H6;apply SinCXXXVII with (P:=U)(a:=a ∩ neg S);split;[ assumption |
     split;[ assumption | rewrite OntoT134;split;assumption ]]]].
Qed.

Lemma SinCLIX : forall P Q R, eta P (plus Q R) -> eta R (relCompl Q P).
Proof.
intros P Q R H;rewrite plus_r in H;destruct H as [H1 H2];assert (eta Q (el P)).
- apply SinLXXXV;exists (Q ∪ R);hauto use: N1, Exterior, OntoT157.
- apply SinXXXII in H1;assert (eta R (el P)).
  -- rewrite SinLXXXV;exists (Q ∪ R);hauto use: N1, Exterior, OntoT157.
  -- rewrite SinCXLV;split;[ assumption |
     apply SinLV;split;[ destruct H0;assumption |
     split;[ intros S H3;apply (SinCXLII P Q R S);split;[ destruct H0;assumption |
     split;[ assumption | strivial use: OntoT134 unfold: el, n_conjunction, ext ]] |
     intros S H3;exists R, S;hauto use: SinXIX, OntoT133 unfold: ext, n_conjunction, el, incl, eta ]]].
Qed.

Lemma SinCLXI : forall P Q R, eta P (plus Q R) -> eta R (pt P).
Proof.
intros P Q R H;apply SinCLIX in H;apply SinXLIII in H;assumption.
Qed.

Lemma SinCLXII : forall P Q R, eta P (plus Q R) -> eta Q (pt P).
Proof.
intros;apply SinCLIX in H;apply SinXLVI with (P:=R);auto.
Qed.

Lemma WSP : forall A B AB, eta AB (relCompl A B) -> exists C, eta C (ext A) /\ eta C (pt B).
Proof.
strivial use: SinXXXVI, SinXLIII.
Qed.

Lemma Sum : forall P a, eta P (sum a) <-> (eta P (klass a) /\ forall Q R, eta Q a /\ eta R a -> eta Q R \/ eta Q (ext R)).
Proof.
intros P a;split.
- intro H;assert (H':=H);solve_op_in_hyp H sum x;destruct H2;[
  destruct H1 as [[H2 H3] H1];split;[ hauto use: incl_equivl unfold: klass, eta, ι | sfirstorder ] | sfirstorder ].
- intro H;destruct H as [H H1];assert (H0:=H);destruct H as [[x H] H2];unfold eta;split;[ destruct H0;assumption |
  apply in_in_singleton with (A:=x);split;[ assumption |
  unfold In;unfold sum;unfold IF_then_else;simpl;apply propositional_extensionality;split;[ auto |
  intro;classical_left;split;[ sfirstorder use: N9, In_singleton_incl_equiv, eta_singleton_l, equiv_singleton unfold: eta, incl | auto ]]]].
Qed.

Lemma SinCLXXVI : forall P Q R, eta P (sum (Q ∪ R)) /\ Individual Q /\ Individual R /\ ~eta Q R -> eta P (plus Q R).
Proof.
intros P Q R [H1 [H2 [H3 H4]]];rewrite Sum in H1;rewrite plus_r;destruct H1;specialize (H0 Q R);assert (eta Q (Q ∪ R) ∧ eta R (Q ∪ R)).
- hfcrush use: N1, D8.
- apply H0 in H1;clear H0;split;[ destruct H1;[ contradiction | assumption ] | assumption ].
Qed.

Lemma SinCLXXVII : forall P, eta P P -> eta P (sum P).
Proof.
hauto lq: on use: Indiv_cv, Sum, MieT11, N5 unfold: eta, sum, klass, singular_eq.
Qed.

Lemma SinCLXXIX : forall P a b, eta P (sum a) /\ (forall Q, eta Q a <-> eta Q b) -> eta P (sum b).
Proof.
intros P a b;repeat rewrite Sum;intros [[H1 H2] H3];split;[ sauto use: SinLXII | intros Q R H4;fcrush ].
Qed.

Lemma SinCLXXX : forall P a, eta P (coll a) /\ (forall Q R, eta Q a /\ eta R a -> eta Q R) -> eta P (sum a).
Proof.
hfcrush use: SinXXI, SinXCIV, Sum, N5 unfold: klass, sum, coll.
Qed.

Lemma SinCLXXXI : forall P Q R, eta P (plus Q R) -> eta P (sum (Q ∪ R)). 
Proof.
intros P Q R H;assert (H0:=H);rewrite plus_r in H;rewrite Sum;destruct H;split.
- auto.
- intros S T H2;assert (set_eq S T \/ eta S (ext T));[ apply SinCIL with (P:=P)(Q:=Q)(R:=R);sauto |
  destruct H3;[ classical_left;strivial use: set_eq_sym, singular_eq_dec unfold: eta, n_disjunction, singular_eq | hauto ]].
Qed.

Lemma SinCLXXXII : forall P Q a b R S, eta P (sum a) /\ eta Q (sum b) /\ eta Q (ext P) /\ eta R a /\ eta S b -> eta R (ext S).
Proof.
intros P Q a b R S [H1 [H2 [H3 [H4 H5]]]];rewrite Sum in H1, H2;destruct H1 as [H1 K1], H2 as [H2 K2];apply SinCXXXVII with (P:=Q)(a:=b);split.
- auto.
- split;[ apply MieT3 with (B:=R) in H1;[ apply SinXXXII in H3;apply ext_el with (P:=P);sfirstorder | auto ] | auto ].
Qed.

Lemma SinCLXXXIII : forall P Q a b R S, eta P (sum a) /\ eta Q (sum b) /\ eta P (ext Q) /\ (eta R a \/ eta R b) /\ (eta S a \/ eta S b) -> eta R S \/ eta R (ext S).
Proof.
intros P Q a b R S [H1 [H2 [H3 [H4 H5]]]];destruct H4.
- destruct H5;[ hauto lq: on use: Sum unfold: sum, ext | classical_right;apply (SinCLXXXII P Q a b);strivial use: SinXXXII ].
- destruct H5;[ classical_right;apply SinXXXII;apply (SinCLXXXII P Q a b);strivial use: SinXXXII | hauto lq: on use: Sum unfold: sum, ext ].
Qed.

Lemma SinCLXXXIV : forall P Q a b R, eta P (sum a) /\ eta Q (sum b) /\ eta R (plus P Q) -> eta R (sum (a ∪ b)).
Proof.
intros P Q a b R [H1 [H2 H3]];assert (K1:=H1);assert (K2:=H2);rewrite Sum;split.
-  apply (SinLXVI P Q);rewrite Sum in H1, H2;rewrite plus_r in H3;sfirstorder.
- intros S T [H4 H5];rewrite Sum in H1, H2;rewrite OntoT157 in *;rewrite plus_r in H3;destruct H3 as [H3 H6];apply (SinCLXXXIII P Q a b);fcrush.
Qed.

(** sum is unique **)

Lemma SinCLXXXV : forall P Q a, eta P (sum a) /\ eta Q (sum a) -> eta P Q.
Proof. 
intros P Q a [H1 H2];rewrite Sum in *;destruct H1 as [H1 K1], H2 as [H2 K2];clear K1 K2;assert (P ≡ Q);
[ apply klUniq with (a:=a);split;assumption | sfirstorder ].
Qed.

Lemma SinCLXXXVI : forall P a, eta P (klass a) /\ (forall Q R, eta Q a /\ eta R (klass (a ∩ (neg Q))) -> eta P (plus Q R)) -> eta P (sum a).
Proof.
intros P a [H1 H2]. assert(forall P S T a, (forall Q R, eta Q a /\ eta R (klass (a ∩ (neg Q))) -> eta P (plus Q R)) /\ eta S a /\ eta T a -> ~(eta S T) -> eta S (ext T)).
- apply SinCLIV.
- rewrite Sum;split.
  -- auto.
  -- intros S T [H3 H4];assert (¬ eta S T → eta S (ext T));[
     specialize (H P S T a);apply SinCLIV with (P:=P)(a:=a);sfirstorder | apply imply_to_or in H0;rewrite <-notnot in H0;assumption ].
Qed.

Lemma SinCLXXXVIII : forall P Q R a, eta P (sum a) /\ eta Q a /\ eta R (klass (a ∩ (neg Q))) -> eta P (plus Q R).
Proof.
intros P Q R a [H1 [H2 H3]];assert (K1:=H2);assert (K2:=H1);apply MieT10 in K1;rewrite Sum in H1;destruct H1 as [H0 H1];assert (forall S, eta S a <-> eta S (Q ∪ (a ∩ (neg Q)))).
- intro S;split.
  -- intro H;rewrite <-OntoT183;assert (Q ∪ neg Q ≈ V);[ apply OntoT233 |
     rewrite OntoT134;split;[ hfcrush use: OntoT157 | sfirstorder ]].
  -- intro;assert ((Q ∪ a) ∩ (Q ∪ neg Q) ≈ Q ∪ (a ∩ neg Q));[ apply OntoT236 |
     rewrite weak_eq_to_set_eq in H4;rewrite N22 in H4;rewrite <-H4 in H;clear H4;apply OntoT134 in H;destruct H;assert (Q ∪ neg Q ≈ V);[
     apply OntoT233 | rewrite weak_eq_to_set_eq in H5;rewrite N22 in H5;rewrite H5 in H4;clear H5;rewrite OntoT157 in H;destruct H;[
     apply OntoT7 with (B:=Q);split;assumption | assumption ]]].
- assert (eta P (klass (Q ∪ (a ∩ neg Q)))).
  -- apply SinLXII with (a:=a);split;assumption.
  -- assert (eta P (klass (Q ∪ R))).
     --- apply (SinLXXV Q R P Q (a ∩ neg Q));sfirstorder.
     --- assert (forall S, eta S (a ∩ neg Q) -> eta Q (ext S));[
         intros S K3;rewrite OntoT134 in K3;destruct K3 as [K3 K4];apply neg_eta in K4;specialize (H1 S Q);assert (eta S Q ∨ eta S (ext Q));[
         apply H1;split;assumption | destruct H6;[ contradiction | apply SinXXXII;assumption ]] |
         assert (eta Q (ext R));[ apply SinCXXXVIII with (a:=a ∩ neg Q);split;assumption | rewrite plus_r;split;assumption ]].
Qed.

Lemma SinCLXXXIX : forall P a, eta P (sum a) <-> (eta P (klass a) /\ (forall Q R, eta Q a /\ eta R (klass (a ∩ (neg Q))) -> eta P (plus Q R))).
Proof.
intros P a;split;[ intro;split;[ rewrite Sum in H;destruct H;assumption | intros Q R [H1 H2];apply SinCLXXXVIII with (a:=a);sfirstorder ] |
intro;apply SinCLXXXVI;sfirstorder ].
Qed.

Lemma SinCXC : forall P Q R, eta P (plus Q R) <-> (eta P (sum (Q ∪ R)) /\ Individual Q /\ Individual R /\ ~eta Q R).
Proof.
intros P Q R;split.
- intro;split.
  -- apply SinCLXXXI in H;assumption.
  -- assert (H0:=H);apply SinCLXII in H;split.
    --- destruct H;assumption.
    --- split;[ apply SinCXLVIII in H0;destruct H0;assumption |
        intro;assert (~eta P (plus Q Q));[ apply SinCXLVII |
        assert (Individual Q /\ Individual R);[ split;[ destruct H1;auto | apply SinCXLVIII in H0;destruct H0;auto ] |
        assert (eta R Q);[  hauto lq: on use: N1, OntoT6 |
        assert (Q ≡ R);[ sfirstorder | hauto lq: on use: Exterior, SinII, LejT0, singular_eq_eq_obj, plus_r ]]]]].
- apply SinCLXXVI.
Qed.

Lemma subset_incl : forall a a' A A', eta A (klass a) /\ eta A' (klass a') -> (a' ⊆ a -> eta A' (coll a)).
Proof.
intros a a' A A' [H1 H2] H3;rewrite Klass in H1, H2;destruct H1 as [K1 [K2 K3]], H2 as [K4 [K5 K6]];
unfold weakInclusion in H3;rewrite Collection;split;[ auto | hfcrush unfold: el ].
Qed. 

Lemma subset_inv : forall a a' A A', eta A (klass a) /\ eta A' (klass a') -> (eta A' (coll a) -> forall Ax, eta Ax (el A') -> eta Ax (el A)).
Proof.
intros a a' A A' [H1 H2] H3;intros B H4;apply SinXXVI in H3;assert (H0:=H1);apply MieT24 in H1;assert (Individual A /\ Individual (klass a)).
- hauto lq: on.
- apply singular_eq_dec in H;rewrite <-H in H1;clear H;assert (eta A' (el A)).
-- apply MieT18 with (B:=klass a);split;sfirstorder.
-- apply SinXXIII with (Q:=A');sfirstorder.
Qed.

Lemma subset_inv_sum : forall a a' A A', eta A (sum a) /\ eta A' (sum a') -> (eta A' (coll a) -> forall Ax, eta Ax (el A') -> eta Ax (el A)).
Proof.
hauto depth: 2 lq: on exh: on use: Sum, subset_inv.
Qed.

Unset Hammer Vampire. 

Lemma ClayT30 : forall A a, eta A (klass a) -> (Individual A /\ forall B, (forall C, eta C a -> eta C (el B)) <-> eta A (el B)).
Proof.
intros A a H1;assert (H0:=H1);rewrite Klass in H1;destruct H1 as [H1 [H2 H3]];split.
- assumption.
- intro B;split.
  -- intro;apply MieT2 in H0;destruct H0 as [E H0];assert (H4:=H0);apply H2 in H0;apply H in H4;apply SinXXVII;split.
     --- assumption.
     --- intros F H5;qauto depth: 4 l: on use: SinXXIII unfold: el.
  -- intros;apply H2 in H4;apply SinXXIII with (Q:=A);sfirstorder.
Qed.

End DST_signature.




