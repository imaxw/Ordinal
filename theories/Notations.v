
(** Binary relations, some duplicated from standard library *)
Reserved Infix "==" (at level 70).
Reserved Infix "=/=" (at level 70).
Reserved Infix "<" (at level 70).
Reserved Infix "≤" (at level 70).
Reserved Infix ">" (at level 70).
Reserved Infix "≥" (at level 70).
Reserved Infix "≶" (at level 70).


(** Conjunctions of binary relations *)
Reserved Notation "x == y == z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x ≤ y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y < z" (at level 70, y at next level).
Reserved Notation "x < y ≤ z" (at level 70, y at next level).
Reserved Notation "x < y == z" (at level 70, y at next level).
Reserved Notation "x == y < z" (at level 70, y at next level).
Reserved Notation "x < y == z" (at level 70, y at next level).
Reserved Notation "x == y < z" (at level 70, y at next level).
Reserved Notation "x ≤ y == z" (at level 70, y at next level).
Reserved Notation "x == y ≤ z" (at level 70, y at next level).

(** Binary operators *)
Reserved Infix "+" (at level 50, left associativity).
Reserved Infix "⋅" (at level 40, left associativity).
Reserved Infix "^" (at level 30, right associativity).

(** Operators on functions mapping into a type *)
Reserved Notation "'min' { F | x : A }".
Reserved Notation "'sup' { F | x : A }".
Reserved Notation "'sup⁺' { F | x : A }".
Reserved Notation "∑ { F | x : A }".
Reserved Notation "∏ { F | x : A }".

(** Operators on predicates upon a type *)
Reserved Notation "'min' { x | P }".
Reserved Notation "'min' { x | P & Q }".
Reserved Notation "'min' { x | P & Q & R }".
