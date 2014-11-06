(** 5. Lógica de primer orden y proposiciones. *)

(** Coq usa el tipo Prop para tratar proposiciones lógicas.
    Una proposición es todo aquello que pueda ser potencialmente demostrado. *)
Check (2 + 1 = 3).
Check forall n, (n + 2 = 2 + n).

(** La construcción de la lógica intuicionista sobre Coq se hace usando el
    isomorfismo de Curry-Howard y partiendo de que sólo tenemos definida
    la implicación. *)
(** And es un constructor que toma P y Q y devuelve P and Q. *)
Inductive and (P Q:Prop) : Prop :=
  conj: P -> Q -> (and P Q).

(** Or son dos constructores tomando cualquier proposición y creando el or. *)
Inductive or (P Q:Prop) : Prop :=
  | or_intro1: P -> or P Q
  | or_intro2: Q -> or P Q.

(** Iff se define en función de lo anterior. *)
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).


Notation "P /\ Q" := (and P Q) : type_scope.
Notation "P \/ Q" := (or P Q) : type_scope.
Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.


(** Y podemos probar ahora teoremas básicos sobre lógica.
    Aquí hay que notar que, aunque bool sea similar a Prop, se refieren
    a distintas cosas. Bool es un tipo con dos constructores y Prop
    se refiere a todas las proposiciones, con muchos constructores de
    por medio. *)
(** La táctica "inversion" permite acudir al constructor de H. *)
Theorem proj1:
  forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HP.
Qed.

Theorem or_comm:
  forall P Q : Prop, P \/ Q -> Q \/ P. 
Proof.
  intros P Q H.
  destruct H.
  apply or_intro2. apply H.
  apply or_intro1. apply H.
Qed.

Theorem and_assoc: 
  forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  apply conj.
    apply conj.
      apply HP.
      apply HQ.
    apply HR.
Qed.


(** Definimos ahora las constantes True y False.
    False será un tipo sin constructores, y por tanto no podrá probarse.
    True será un tipo con una constante definida, y por tanto poblado.
    La negación se define en función de esto. *)
Inductive False : Prop := .
Inductive True : Prop := I : True.
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.  


(** Y podemos usarlas para probar proposiciones.
    Ahora se notará el problema de la lógica intuicionista, no hay
    forma de demostrar el tercio excluso. Si lo queremos probar, debemos
    tomarlo nosotros como axioma. *)
(** La táctica "unfold" permite reescribir por la definición. *) 
Theorem not_false:
  ~ False.
Proof.
  unfold not.
  intros H.
  apply H.
Qed.

Theorem ex_falso_quodlibet:
  forall (P:Prop), False -> P.
Proof.
  intros P HF.
  destruct HF.
Qed.

Theorem excluded_middle:
  forall P:Prop, P \/ ~P.
Proof.
  intros P.
  (** No hay forma de probarlo *)
Abort.

(** Pero podemos tomarlo como axioma. *)
Definition excluded_middle := forall P:Prop, P \/ ~P.



(** Las proposiciones de lógica de primer orden pueden probarse
    más generalmente con la técnica "firstorder", que aprovecha que
    la lógica de primer orden es completa para intentar demostrar
    cualquier proposición. *)
Theorem frobenius: 
  forall (A : Set) (p : A -> Prop) (q : Prop), 
   (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
Proof.
  firstorder.
Qed.

(** Y como la aritmética de Presburguer también es completa,
    la táctica omega resuelve proposiciones aritméticas. *)
Require Import Omega.

Theorem arithm:
  forall (n m:nat), 1 + 2*m <> 2*n.
Proof.
  intros n m.
  omega.
Qed.