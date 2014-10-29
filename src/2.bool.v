(** 2. El tipo de los booleanos. *)

(** Vamos a definir el tipo booleano, varias
    funciones entre booleanos y varios teoremas
    sobre sus relaciones.
    Después usaremos el tipo desde la librería estándar. *)
Inductive bool : Type :=
  | true : bool
  | false : bool.



(** Funciones sobre los booleanos.
    Nótese cómo podemos definir la mayoría de funciones
    condensándolas en una única definición del 'if',
    de la que surgen como casos particulares. *)
Definition ifb (a b c:bool) : bool := 
  match a with
    | true => b
    | false => c
  end.

Definition andb (a b:bool) : bool :=
  ifb a b false.

Definition orb (a b:bool) : bool :=
  ifb a true b.

Definition negb (a:bool) : bool :=
  ifb a false true.

Definition xorb (a b:bool) : bool :=
  match a,b with
    | true, true => false
    | true, false => true
    | false, true => true
    | false, false => false
  end.



(** Propiedades de las funciones *)
(** La técnica "intros" instancia las variables libres
    en hipótesis que se pueden tratar. *) 
Lemma andb_commutative:
  forall (a b:bool),  andb a b = andb b a.
Proof.
  intros a b.
  destruct a.
  destruct b.
  reflexivity.
  reflexivity.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Lemma orb_commutative:
  forall (a b:bool),  orb a b = orb b a.
Proof.
  intros a b.
  destruct a.
  destruct b. reflexivity. reflexivity.
  destruct b. reflexivity. reflexivity.
Qed.

Lemma xorb_commutative:
  forall (a b:bool),  xorb a b = xorb b a.
Proof.
  intros a b.
  destruct a.
  destruct b. reflexivity. reflexivity.
  destruct b. reflexivity. reflexivity.
Qed.

Lemma negb_involutive:
  forall (b:bool), negb (negb b) = b.
Proof.
  intros b.
  destruct b. reflexivity. reflexivity.
Qed.  



(** La técnica "rewrite" sirve para usar un teorema anterior
    para sustituir un término de la ecuación actual. 
    La dirección de la sustitución se añade en una flecha delante
    de la orden. *)
Lemma xorb_false_r:
  forall (a:bool),  xorb a false = a.
Proof.
  destruct a.
  reflexivity. reflexivity.
Qed.

Lemma xorb_false_l:
  forall (a:bool), xorb false a = a.
Proof.
  intros a.
  rewrite <- xorb_commutative.
  rewrite -> xorb_false_r.
  reflexivity.
Qed.



(** La técnica "rewrite" puede usarse con teoremas instanciados
    con argumentos. A un teorema se le pueden pasar como argumentos
    los valores sobre los que se aplica. *)
Theorem morgan_law1:
  forall (a b:bool), andb (negb a) (negb b) = negb (orb a b).
Proof. 
  intros a b.
  destruct a. 
  destruct b. reflexivity. reflexivity.
  destruct b. reflexivity. reflexivity.
Qed.

Theorem morgan_law2:
  forall (a b:bool), negb (andb a b) = orb (negb a) (negb b).
Proof.
  intros a b.
  rewrite <- (negb_involutive a).
  rewrite <- (negb_involutive b).
  rewrite -> morgan_law1.
  rewrite -> (negb_involutive a).
  rewrite -> (negb_involutive b).
  rewrite -> negb_involutive.
  reflexivity.
Qed.