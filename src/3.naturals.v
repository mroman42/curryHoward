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
