(** 4. Listas y polimorfismo *)

(** Coq permitirá definiciones de tipos polimórficos. Serán tipos 
    parametrizados sobre un tipo. El ejemplo canónico son las listas
    sobre un tipo. *)
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.


(** Para que sea más sencillo tratar con tipos parametrizados sin estar
    siempre especificando el tipo X, podemos señalarlo como argumento
    implícito. En las siguientes definiciones lo marcaremos entre llaves.*)
Arguments nil {X}.
Arguments cons {X} _ _.

(** Y para que sea más sencillo trabajar con listas introducimos la notación
    asociada habitual. *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** La operación básica en listas será la unión. *)
Fixpoint append {X:Type} (l t:list X) : list X :=
  match l,t with
    | [], t => t
    | x::xs, t => x :: (append xs t)
  end.

Notation "x ++ y" := (append x y) (at level 60, right associativity).

(** Definimos funciones usando inducción sobre listas. Nótese que aquí
    la inducción es inducción estructural sobre los constructores de lista. *)
Fixpoint length {X:Type} (l:list X) : nat :=
  match l with
    | [] => 0
    | x :: xs => S (length xs)
  end.

Eval compute in length (cons 4 (cons 2 (cons 3 nil))).

Fixpoint snoc {X:Type} (l:list X) (x:X) : list X :=
  match l,x with
    | [], x => x :: []
    | u :: us, x => u :: (snoc us x)
  end.

Fixpoint reverse {X:Type} (l:list X) : list X :=
  match l with
    | [] => []
    | x :: xs => snoc (reverse xs) x
  end.

Eval compute in reverse (cons 4 (cons 2 (cons 3 nil))).


(** Ahora tratamos teoremas sobre las listas. Usaremos inducción
    estructural para demostrarlos. *)
Theorem nat_list_homeomorphism:
  forall {X:Type} (xs ys:list X),  length (xs ++ ys) = length xs + length ys.
Proof.
  intros X xs ys.
  induction xs as [|x xss].
    reflexivity.
    simpl. rewrite -> IHxss. reflexivity.
Qed.
