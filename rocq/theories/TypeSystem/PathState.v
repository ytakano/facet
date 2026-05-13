From Facet.TypeSystem Require Import Types Syntax.
From Stdlib Require Import List String Bool.
Import ListNotations.

Definition field_path := list string.

Definition path_segment_eqb (a b : string) : bool := String.eqb a b.

Fixpoint path_eqb (p q : field_path) : bool :=
  match p, q with
  | [], [] => true
  | x :: xs, y :: ys => path_segment_eqb x y && path_eqb xs ys
  | _, _ => false
  end.

Fixpoint path_prefix_b (prefix path : field_path) : bool :=
  match prefix, path with
  | [], _ => true
  | x :: xs, y :: ys => path_segment_eqb x y && path_prefix_b xs ys
  | _ :: _, [] => false
  end.

Definition path_conflict_b (p q : field_path) : bool :=
  path_prefix_b p q || path_prefix_b q p.

Fixpoint path_conflicts_any_b (p : field_path) (paths : list field_path) : bool :=
  match paths with
  | [] => false
  | q :: rest => path_conflict_b p q || path_conflicts_any_b p rest
  end.

Fixpoint remove_restored_paths (p : field_path) (paths : list field_path) : list field_path :=
  match paths with
  | [] => []
  | q :: rest =>
      if path_prefix_b p q
      then remove_restored_paths p rest
      else q :: remove_restored_paths p rest
  end.

Record binding_state : Type := MkBindingState {
  st_consumed : bool;
  st_moved_paths : list field_path
}.

Definition binding_state_of_bool (b : bool) : binding_state :=
  MkBindingState b [].

Definition binding_available_b (st : binding_state) (p : field_path) : bool :=
  negb (st_consumed st) && negb (path_conflicts_any_b p (st_moved_paths st)).

Definition state_consume_path (p : field_path) (st : binding_state) : binding_state :=
  match p with
  | [] => MkBindingState true (st_moved_paths st)
  | _ => MkBindingState (st_consumed st) (p :: st_moved_paths st)
  end.

Definition state_restore_path (p : field_path) (st : binding_state) : binding_state :=
  MkBindingState (st_consumed st) (remove_restored_paths p (st_moved_paths st)).

Fixpoint place_path (p : place) : option (ident * field_path) :=
  match p with
  | PVar x => Some (x, [])
  | PField q f =>
      match place_path q with
      | Some (x, path) => Some (x, path ++ [f])
      | None => None
      end
  | PDeref _ => None
  end.

Fixpoint place_suffix_path (p : place) : field_path :=
  match p with
  | PVar _ => []
  | PDeref _ => []
  | PField q f => place_suffix_path q ++ [f]
  end.
