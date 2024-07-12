Require Export Fiat.Common Fiat.Computation.

Require Export Fiat.Examples.Tutorial.Refinement.

Record refinableType := {
    A : Type ;
    ARef : Refinable A
  }.

Definition refinableType_toType (x : refinableType) := x.(A).

Coercion refinableType_toType : refinableType >-> Sortclass.

Existing Class refinableType.
Instance refTypeAuto A (HA : Refinable A) : refinableType.
econstructor. exact HA.
Defined.

#[export]
Notation "↑ A" := (@refTypeAuto A _) (at level 10).

(** Type of a constructor. *)
Fixpoint constructorType (rep : Type)
         (dom : list Type) : Type :=
  match dom with
  | nil =>
    Comp rep (* Freshly constructed model *)
  | cons d dom' =>
    d -> constructorType rep dom' (* Initialization arguments *)
  end.

(** Type of a method. *)
Fixpoint methodType' (rep : Type)
         (dom : list Type)
         (cod : option refinableType) : Type :=
  match dom with
  | nil =>
    match cod with
    | Some cod' => Comp (rep * cod') (* Final model and a return value *)
    | _ => Comp rep
    end
  | cons d dom' =>
    d -> methodType' rep dom' cod (* Method arguments *)
  end.


Definition methodType (rep : Type)
           (dom : list Type)
           (cod : option refinableType) : Type :=
  rep -> methodType' rep dom cod.

(* Signatures of ADT operations *)
Record ADTSig :=
  {
    (** The index set of constructors *)
    ConstructorIndex : Type;

    (** The index set of methods *)
    MethodIndex : Type;

    (** The representation-independent domain of constructors. *)
    ConstructorDom : ConstructorIndex -> list Type;

    (** The representation-independent domain and codomain of methods. *)
    MethodDomCod : MethodIndex -> (list Type) * (option refinableType)

  }.
