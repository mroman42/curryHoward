(** Por el isomorfismo de Curry-Howard, 
    la declaración de "beautiful" puede interpretarse de dos maneras:
     - Es un tipo parametrizado en los naturales. Devuelve un tipo por natural.
     - Es una proposición sobre los naturales. Hay una proposición por natural.
    podemos leer las definiciones de dos formas distintas:
     - "b_0" es una instancia del tipo "beautiful 0".
     - "b_0" es una demostración (axiomática) de "beautiful 0".
   *)
Inductive beautiful : nat -> Prop :=
  | b_0 : beautiful 0
  | b_3 : beautiful 3
  | b_5 : beautiful 5
  | b_sum : forall n m : nat,  beautiful n -> beautiful m -> beautiful (n+m).


(** Y si ahora demostramos un teorema sobre esta proposición.
    O, de otra forma, construimos un objeto de tipo beautiful 8. *)
(* Teorema / Declaración de tipos *)
Theorem eight_is_beautiful : beautiful 8.
(* Demostración / Construcción *)
Proof.
  apply b_sum with (n:=3) (m:=5).
  apply b_3.
  apply b_5.
Qed.

(* Y podemos mirar el objeto/teorema construido. *)
Print eight_is_beautiful.

(* También podemos mirar a cada paso cómo se construye el objeto.
   Los argumentos que le faltan al constructor empiezan por "?". *)
Theorem eight_is_beautiful2 : beautiful 8.
Proof.
  Show Proof.
  apply b_sum with (n:=3) (m:=5).
  Show Proof.
  apply b_3.
  Show Proof.
  apply b_5.
  Show Proof.
Qed.


(** Y desde aquí, podemos pedir a un ordenador que demuestre
    teoremas. *)
Require Import Omega.
Theorem par_e_impar:
  forall (n m:nat),  2*n <> 2*m+1.
Proof.
  intros n m.
  omega.
Qed.

(** Y esta monstruosidad es la demostración que acaba de marcarse. *)
Print par_e_impar.