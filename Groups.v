Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Definition groupId : Type := nat.
Definition userId : Type := nat.

Inductive group : Type := Group (id : groupId) (children : list group) (members : list userId).

Definition is_some {X : Type} (o : option X) : bool :=
  match o with
  | None => false
  | Some _ => true
  end.

Fixpoint has_access' (g : group) (gid : groupId) (uid : userId) (accessToParent : bool) : bool :=
  match g with
  | Group gid' children members => 
    let has_access_here := is_some (find (fun uid' => eqb uid uid') members) in
    if eqb gid gid'
      then accessToParent || has_access_here
      else existsb (fun gg => has_access' gg gid uid (accessToParent || has_access_here)) children
  end.