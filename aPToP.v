Section aPToP.

Variable bunch: Type. (* all terms of the theory have that type *)
Variable true false: bunch.


(* 0 : L0 *)
Notation "'T'" := true.
Notation "'⊥'" := false.
Variable set: bunch -> bunch.
Notation " { A } " := (set A) (at level 0, A at level 99).
Variable list: bunch -> bunch.
Notation " [ A ] " := (list A) (at level 0, A at level 200).
Variable scope: bunch -> (bunch -> bunch) -> bunch.
Notation " ‹ x ː D → e › " := (scope D (fun x: bunch => e)) (at level 0, e at level 200).
Variable exponentiation: bunch -> bunch -> bunch.
Notation "A ¯ B" := (exponentiation A B) (at level 0, right associativity).
Variable string_indexing: bunch -> bunch -> bunch.
Notation "A '._.' B" := (string_indexing A B) (at level 0, right associativity).

(* 1 : L10 *)
Variable index: bunch -> bunch -> bunch.
Notation "A '@' I" := (index A I) (at level 10, left associativity).
Variable apply: bunch -> bunch -> bunch.
Notation "A ○ I" := (apply A I) (at level 10, left associativity).

(* 2 : L35 *)
Variable opposite: bunch -> bunch.
Notation "- A" := (opposite A) (at level 35, right associativity).
Variable bunch_size: bunch -> bunch.
Notation "'¢' A" := (bunch_size A) (at level 35, right associativity).
Variable set_size: bunch -> bunch.
Notation "'$' A" := (set_size A) (at level 35, right associativity).
Variable string_size: bunch -> bunch.
Notation "'↔' A" := (string_size A) (at level 35, right associativity).
Variable list_size: bunch -> bunch.
Notation "'#' A" := (list_size A) (at level 35, right associativity).
Variable copies: bunch -> bunch -> bunch.
Notation "A ¤ B" := (copies A B) (at level 35, right associativity).
Variable set_content: bunch -> bunch.
Notation "'˜ ' A" := (set_content A) (at level 35, right associativity).
Variable list_content: bunch -> bunch.
Notation "'ͷ' A" := (list_content A) (at level 35, right associativity).
Variable power: bunch -> bunch.
Notation "'ϟ' A" := (power A) (at level 35, right associativity).
Variable domain: bunch -> bunch.
Notation "'□' A" := (domain A) (at level 35, right associativity).
Variable lamdba: bunch -> bunch -> bunch.
Notation "A '→' B" := (lamdba A B) (at level 35, right associativity).
Variable check: bunch -> bunch.
Notation "'√' A" := (check A) (at level 35, right associativity).

(* 3 : L40 *)
Variable times: bunch -> bunch -> bunch.
Notation "A × B" := (times A B) (at level 40, left associativity).
Variable divide: bunch -> bunch -> bunch.
Notation "A / B" := (divide A B) (at level 40, left associativity).
Variable intercept: bunch -> bunch -> bunch.
Notation "A ∩ B" := (intercept A B) (at level 40, left associativity).

(* 4 : L50 *)
Variable plus: bunch -> bunch -> bunch.
Notation "A + B" := (times A B) (at level 50, left associativity).
Variable minus: bunch -> bunch -> bunch.
Notation "A - B" := (minus A B) (at level 50, left associativity).
Variable list_catenation: bunch -> bunch -> bunch.
Notation "A ˖ B" := (list_catenation A B) (at level 50, left associativity).
Variable union: bunch -> bunch -> bunch.
Notation "A ∪ B" := (union A B) (at level 50, left associativity).

(* 5 : L55 *)
Variable string_catenation: bunch -> bunch -> bunch.
Notation "A ; B" := (string_catenation A B) (at level 55, left associativity).
Variable string_range: bunch -> bunch -> bunch.
Notation "A ;.. B" := (string_range A B) (at level 55, left associativity).
Variable bunch_intercept: bunch -> bunch -> bunch.
Notation "A ‘ B" := (bunch_intercept A B) (at level 55, left associativity).

(* 6 : L60 *)
Variable bunch_union: bunch -> bunch -> bunch.
Notation "A , B" := (bunch_union A B) (at level 60, right associativity).
Variable bunch_range: bunch -> bunch -> bunch.
Notation "A ,.. B" := (bunch_range A B) (at level 60, right associativity).
Variable otherwise: bunch -> bunch -> bunch.
Notation "A | B" := (otherwise A B) (at level 60, right associativity).
Variable replace : bunch -> bunch -> bunch -> bunch.
Notation "A ◃ B ▹ C" := (replace A B C) (at level 60, right associativity).

(* 7 : L70 *)
Variable is: bunch -> bunch -> bunch.
Notation "A ː B" := (is B A) (at level 70).
Variable equal: bunch -> bunch -> bunch.
Notation "A = B" := (equal A B) (at level 70).
Variable different: bunch -> bunch -> bunch.
Notation "A ≠ B" := (different A B) (at level 70).
Variable lt: bunch -> bunch -> bunch.
Notation "A < B" := (lt A B) (at level 70).
Variable gt: bunch -> bunch -> bunch.
Notation "A > B" := (gt A B) (at level 70).
Variable le: bunch -> bunch -> bunch.
Notation "A ≤ B" := (le A B) (at level 70).
Variable ge: bunch -> bunch -> bunch.
Notation "A ≥ B" := (ge A B) (at level 70).
Variable includes: bunch -> bunch -> bunch.
Notation "A ∷ B" := (includes B A) (at level 70).
Variable of: bunch -> bunch -> bunch.
Notation "A ∊ B" := (of B A) (at level 70).
Variable subset: bunch -> bunch -> bunch.
Notation "A ⊂ B" := (subset B A) (at level 70).


(* 8 : L71 *)
Variable not: bunch -> bunch.
Notation "¬ A" := (not A) (at level 71, right associativity).

(* 9 : L72 *)
Variable and: bunch -> bunch -> bunch.
Notation "A ∧ B" := (and A B) (at level 72, right associativity).

(* 10: L73 *)
Variable or: bunch -> bunch -> bunch.
Notation "A ∨ B" := (or A B) (at level 73, right associativity).

(* 11: L74 *)
Variable imply: bunch -> bunch -> bunch.
Notation "A ⇒ B" := (imply A B) (at level 74, right associativity).
Variable impliedby: bunch -> bunch -> bunch.
Notation "A ⇐ B" := (impliedby A B) (at level 74, right associativity).

(* 15: L80 *)
Variable all: bunch -> bunch -> bunch.
Notation "∀ A" := (all A) (at level 80, right associativity).
Notation "∀ x ː D · e" := (all (scope D (fun x: bunch => e))) (at level 80, left associativity).
Variable some: bunch -> bunch -> bunch.
Notation "∃ A" := (some A) (at level 80, right associativity).
Notation "∃ x ː D · e" := (some (scope D (fun x: bunch => e))) (at level 80, left associativity).
Variable sum: bunch -> bunch -> bunch.
Notation "'Σ' A" := (sum A) (at level 80, right associativity).
Notation "'Σ' x ː D · e" := (sum (scope D (fun x: bunch => e))) (at level 80, left associativity).
Variable prod: bunch -> bunch -> bunch.
Notation "'Π' A" := (prod A) (at level 80, right associativity).
Notation "'Π' x ː D · e" := (prod (scope D (fun x: bunch => e))) (at level 80, left associativity).
Variable find: bunch -> bunch -> bunch.
Notation "'§' A" := (find A) (at level 80, right associativity).
Notation "'§' x ː D · e" := (find (scope D (fun x: bunch => e))) (at level 80, left associativity).
Variable limit: bunch -> bunch -> bunch.
Notation "'LIM' A" := (limit A) (at level 80, right associativity).
Notation "'LIM' x ː D · e" := (limit (scope D (fun x: bunch => e))) (at level 80, left associativity).
Variable max: bunch -> bunch -> bunch.
Notation "'MAX' A" := (max A) (at level 80, right associativity).
Notation "'MAX' x ː D · e" := (max (scope D (fun x: bunch => e))) (at level 80, left associativity).
Variable min: bunch -> bunch -> bunch.
Notation "'MIN' A" := (min A) (at level 80, right associativity).
Notation "'MIN' x ː D · e" := (min (scope D (fun x: bunch => e))) (at level 80, left associativity).



(* 16: L80 *)
Notation "A ≡ B" := (equal A B) (at level 80).
Notation "A ➪ B" := (imply A B) (at level 80).
Notation "A ⇦ B" := (impliedby A B) (at level 80).

(* 17: L99 *)
Variable th: bunch -> Prop.
Notation "› A" := (th A) (at level 99).

(* 18: L200 *)
Variable ite: bunch -> bunch -> bunch -> bunch.
Notation "'if' A 'then' B 'else' C 'fi'" := (ite A B C) (at level 200).

(* Distribution *)
Variable nil: bunch.
Variable is_elem: bunch -> Prop.
Definition distribute := fun (f: bunch -> bunch) 
=> (› f nil = nil) /\ forall (a b: bunch), f (a,b) = f a, f b.
Definition codistribute := fun (f: bunch -> bunch -> bunch) 
=> forall (c: bunch), distribute (fun x: bunch => f x c) /\ distribute (f c).
Hypothesis dist_list : distribute list.
Hypothesis dist_index : codistribute index.
Hypothesis dist_apply : codistribute apply.
Hypothesis dist_opposite : distribute opposite.
Hypothesis dist_set_size : distribute set_size.
Hypothesis dist_list_size : distribute list_size.
Hypothesis dist_string_size : distribute string_size.
Hypothesis dist_set_content : distribute set_content.
Hypothesis dist_list_content : distribute list_content.
Hypothesis dist_exponentiation : codistribute exponentiation.
Hypothesis dist_string_indexing : codistribute string_indexing.
Hypothesis dist_times : codistribute times.
Hypothesis dist_divide : codistribute divide.
Hypothesis dist_intercept : codistribute intercept.
Hypothesis dist_plus : codistribute plus.
Hypothesis dist_minus : codistribute minus.
Hypothesis dist_list_catenation : codistribute list_catenation.
Hypothesis dist_union : codistribute union.
Hypothesis dist_string_catenation : codistribute string_catenation.
Hypothesis dist_bunch_intercept : codistribute bunch_intercept.
Hypothesis dist_not : distribute not.
Hypothesis dist_or : codistribute or.
Hypothesis dist_and : codistribute and.
Hypothesis dist_copies : forall (c: bunch), distribute (fun x: bunch => copies x c).

(* generic *)
Hypothesis eq_reflexivity: forall (a: bunch), › a=a.
Hypothesis eq_transparency: forall (a b: bunch) (f: bunch -> Prop), › a=b -> f a -> f b.
Hypothesis unequality_def: forall (a b: bunch), › ¬a=b ≡ a≠b.

(* bin *)
Variable bin: bunch.
Definition is_bin := fun x: bunch => (› x = T) \/ (› x=⊥).
Hypothesis bin_def: › bin = T, ⊥.
Hypothesis eq_is_bin: forall (x y: bunch), is_bin (x=y).
Hypothesis bin_elem: forall (x: bunch), is_bin x -> is_elem x.
Hypothesis true_e: › T.
Hypothesis true_i: forall (a: bunch), › a -> › a = T.
Hypothesis false_i: forall (a: bunch), › ¬ a -> › a = ⊥.
Hypothesis eval_not_F: › ¬ ⊥.
Hypothesis eval_not_T: › ¬ ¬ T.
Hypothesis eval_imply_TT: › T ⇒ T.
Hypothesis eval_imply_FT: › ⊥ ⇒ T.
Hypothesis eval_imply_FF: › ⊥ ⇒ ⊥.
Hypothesis eval_imply_TF: › ¬(T ⇒ ⊥).
Hypothesis eval_ite_T: forall (a b: bunch), › if T then a else b fi ≡ a.
Hypothesis eval_ite_F: forall (a b: bunch), › if ⊥ then a else b fi ≡ b.
Hypothesis and_def: forall (a b: bunch), › a∧b ≡ ¬(a⇒¬b).
Hypothesis or_def: forall (a b: bunch), › a∨b ≡ ¬a⇒b.
Hypothesis implied_def: forall (a b: bunch), › a ⇐ b ≡ b ⇒ a.

Theorem eval_imply_TFF: › (T ⇒ ⊥) ⇒ ⊥.
cut (› ⊥ ⇒ ⊥).
cut (› ⊥ = (T ⇒ ⊥)).
exact (eq_transparency _ _ (fun x=> › x ⇒ ⊥)).
cut (› (T ⇒ ⊥) = (T ⇒ ⊥)).
cut (› (T ⇒ ⊥) = ⊥).
exact (eq_transparency _ _ (fun x=> › x = (T ➪ ⊥))).
auto.
auto.
auto.
Qed.

Theorem eval_and_TT: › T∧T.
cut (› ¬(T⇒¬T)).
cut (› ¬(T⇒¬T) ≡ T∧T ).
apply eq_transparency.
cut (› T∧T ≡ T∧T ).
cut (› T∧T ≡ ¬(T⇒¬T) ).
exact (eq_transparency _ _ (fun x=> › x = (T∧T))).
auto.
auto.
cut (› ¬(T ⇒ ⊥)).
cut (› ⊥ ≡ ¬T).
exact (eq_transparency _ _ (fun x=> › ¬(T ⇒ x))).
cut (› ¬T ≡ ¬T).
cut (› ¬T ≡ ⊥).
exact (eq_transparency _ _ (fun x=> › x = ¬T)).
apply false_i.
auto.
auto.
auto.
Qed.

Theorem double_negation_law: forall (a: bunch), is_bin a -> › ¬¬a ≡ a.
unfold is_bin.
intros a h.
destruct h.
cut (› ¬ ¬ T ≡ T).
cut (› T = a).
exact (eq_transparency _ _ (fun x=>› ¬ ¬ x ≡ x)).
cut (› a = a).
cut (› a = T).
exact (eq_transparency _ _ (fun x=> › x = a)).
auto.
auto.
auto.
cut (› ¬ ¬ ⊥ ≡ ⊥).
cut (› ⊥ = a).
exact (eq_transparency _ _ (fun x=>› ¬ ¬ x ≡ x)).
cut (› a = a).
cut (› a = ⊥).
exact (eq_transparency _ _ (fun x=> › x = a)).
auto.
auto.
apply false_i.
cut (› ¬ ¬ T).
cut (› T ≡ ¬ ⊥).
exact (eq_transparency _ _ (fun x=> › ¬ ¬ x)).
cut (› ¬ ⊥ ≡ ¬ ⊥).
cut (› ¬ ⊥ ≡ T).
exact (eq_transparency _ _ (fun x=> › x ≡ ¬ ⊥)).
apply true_i.
auto.
auto.
auto.
Qed.

(* bunch *)
Hypothesis elementary_law: forall (x y: bunch), is_elem x -> is_elem y
-> › xːy ≡ x=y.
Hypothesis compound_law: forall (x A B: bunch), is_elem x 
-> › xːA,B ≡ xːA ∨ xːB.
Hypothesis idempotence: forall (A: bunch), › A,A ≡ A.
Hypothesis symmetry: forall (A B: bunch), › A,B ≡ B,A.

(* ... *)
(* function *)
Hypothesis application_law: forall (D: bunch) (f: bunch->bunch) (x: bunch), is_elem x -> › x ː D ⇒ (scope D f) ○ x = f x.

(* ... *)
