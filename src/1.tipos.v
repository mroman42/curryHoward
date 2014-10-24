(** 1. Definición de tipos, funciones y teoremas **)

(** En Coq, los tipos habituales no son nativos (int, string, bool).
    En lugar de ello, el lenguaje ofrece la capacidad de definir todos estos tipos
    de datos al usuario y los incluye en librerías.
       
    Los tipos se definen por enumeración de sus constructores, que pueden ser
    parametrizados o no. **)

(* Tipo sin parametrizar *)
Inductive season : Type :=
  | spring : season
  | summer : season
  | autumn : season
  | winter : season
.

(* Tipo parametrizado *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat
.


(** En Coq habrá varios tipos de definir funciones.
    Las funciones más simples tomarán un argumento y
    usarán pattern matching, como en Haskell, para
    especificar su imagen. 

    Las funciones podemos probarlas usando:
      Eval compute
    Los tipos se comprueban usando:
      Check *)
Definition next (s:season) : season :=
  match s with
    | spring => summer
    | summer => autumn
    | autumn => winter
    | winter => spring
  end.


Eval compute in next summer.
Check summer.
Check next.


(** Para demostrar un teorema habrá que enunciarlo primero.
    Tras enunciarlo, entramos en el entorno "Proof", donde
    indicamos los pasos a seguir para demostrarlo.

    Nuestro objetivo es solucionar todos los "goal" que
    aparecen al enunciar el teorema. *)

(** La técnica "simpl" simplifica un lado de la ecuación.
    La técnica "reflexivity" comprueba igualdad a ambos lados. *)
Lemma nn_summer_winter:
  next (next summer) = winter.
Proof.
  simpl.
  reflexivity.
Qed.

(** La técnica "destruct" demuestra por casos según los
    constructores del tipo. *)
Theorem nnnn_involutive:
  forall (s:season), (next (next (next (next (s))))) = s.
Proof.
  simpl.
  destruct s.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
Qed.