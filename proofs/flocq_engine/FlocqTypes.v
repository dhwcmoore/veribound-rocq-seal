(* FlocqTypes.v - Definition of verified boundaries and classification *)

Require Import QArith.
Require Import Reals.
Require Import String.
Require Import List.
From Flocq Require Import Core.Defs.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.
Require Import Flocq.Core.Raux.

Open Scope Q_scope.
Open Scope R_scope.
Open Scope string_scope.
Open Scope list_scope.

Definition float64 := binary_float 53 1024.

Definition classification_precision_bound : R := (1 / 1000)%R.

Record VerifiedBoundary := {
  lower_rational : Q;
  upper_rational : Q;
  lower_float : float64;
  upper_float : float64;
  category : string;
  precision_verified :
    (Rabs (Q2R lower_rational - B2R 53 1024 lower_float) < classification_precision_bound) /\
    (Rabs (Q2R upper_rational - B2R 53 1024 upper_float) < classification_precision_bound)
}.

Record VerifiedDomain := mkVD {
  domain_name : string;
  measurement_unit : string;
  boundaries : list VerifiedBoundary;
  global_bounds : float64 * float64;
  domain_precision_bound : R
}.

Definition QtoR (q : Q) : R := Q2R q.

Definition B2R64 (f : float64) : R := B2R 53 1024 f.

Definition in_boundary_range (x : float64) (b : VerifiedBoundary) : bool :=
  match Bcompare 53 1024 b.(lower_float) x with
  | Some Eq => true
  | Some Lt =>
      match Bcompare 53 1024 x b.(upper_float) with
      | Some Lt => true
      | Some Eq => true
      | _ => false
      end
  | _ => false
  end.

Fixpoint find_category_flocq (boundaries : list VerifiedBoundary) (x : float64) : option string :=
  match boundaries with
  | nil => None
  | b :: rest =>
    if in_boundary_range x b then Some b.(category)
    else find_category_flocq rest x
  end.

Definition classify_rational (x : Q) (bounds : list VerifiedBoundary) : string :=
  match bounds with
  | nil => "NO_BOUNDS"%string
  | hd :: _ => hd.(category)
  end.
