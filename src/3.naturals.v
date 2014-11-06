(** 3. Naturales e inducción. *)

(** Ahora vamos a entrar a definir el tipo de los naturales. Al definirlo como
    Inductive, se creará directamente un teorema de inducción estructural sobre
    el tipo; que podremos usar luego para hacer inducción. *)

(** Definimos la aritmética de Peano.
    Tenemos una constante natural "O", y una función que toma un natural
    y devuelve otro. Así, los naturales son de la forma:
     O, (S O), (S S O), (S S S O), ...  *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.



(** Definimos la suma y la multiplicación. 
    Van a ser funciones "Fixpoint", definidas usando la inducción. El intérprete
    sólo nos dejará definirlas cuando pueda comprobar que la inducción termina. *)
Fixpoint plus (n m:nat) : nat :=
  match n with
    | O => m
    | S p => S (plus p m)
  end.

Fixpoint mult (n m:nat) : nat :=
  match n with
    | O => O
    | S p => plus m (mult p m)
  end.

Eval compute in mult (S (S (S O))) (S (S O)).


(** El intérprete permite definir notación auxiliar, aunque no es recomendado usarla
    más que en los casos que sean necesarios. *)
Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity). 
Eval compute in (S (S (S (S O)))) + (S (S O)).
Eval compute in (S (S (S (S O)))) * (S (S O)).



(** Vamos a demostrar teoremas por inducción. *)
Lemma plus_0_r:
  forall (n:nat), n = n + O.
Proof.
  intros n.
  induction n as [|n'].
    reflexivity.
    simpl. rewrite <- IHn'. reflexivity.
Qed.    

Check plus_0_r.

Lemma plus_S_r:
  forall (n m:nat), n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| n'].
    reflexivity.
    simpl. rewrite <- IHn'. reflexivity.
Qed.    

Theorem plus_comm:
  forall (n m:nat), n + m = m + n.
Proof.
  intros n m.
  induction n.
    simpl. rewrite <- plus_0_r. reflexivity.
    simpl. rewrite -> IHn. rewrite -> plus_S_r. reflexivity.
Qed.