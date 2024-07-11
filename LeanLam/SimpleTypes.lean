-- The simply typed lambda calculus
-- https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus#Typing_rules

import Lean.Data.HashMap
import Aesop
open Lean

namespace STLC

inductive Ty where
| Int : Ty
| Unit : Ty
| Arrow : Ty → Ty → Ty
deriving BEq, DecidableEq, Hashable

instance : LawfulBEq Ty where
  rfl {a} := by
    induction a with
    | Int => rfl
    | Unit => rfl
    | Arrow τ τ' ihτ ihτ' => sorry
  eq_of_beq {a b} := by
    induction a generalizing b with
    | Int =>
      cases b
      · simp
      · intros; contradiction
      · intros; contradiction
    | Unit =>
      cases b
      · intros; contradiction
      · simp
      · intros; contradiction
    | Arrow x y ihx ihy =>
      cases b
      · simp [ihx, ihy]
        exact rfl
      · simp [ihx, ihy]
        exact rfl
      · simp [ihx, ihy]
        intro h
        sorry

inductive Exp where
| Var : String → Exp
| Lam : String → Ty → Exp → Exp
| App : Exp → Exp → Exp
| Num : Int → Exp
| Add : Exp → Exp → Exp
| Unit : Exp
deriving BEq, Hashable

abbrev Γ := Lean.HashMap Exp Ty

-- impl 1 --

namespace Impl1

inductive Judgement where
| Judgement (ctx : Γ) (exp : Exp) (ty : Ty) : Judgement

def infer (ctx : Γ) : (exp : Exp) → Option Ty
| .Var s => HashMap.find? ctx (.Var s)
| .Num _ => some .Int
| .Add l r => do
  let lt ← infer ctx l
  let rt ← infer ctx r
  if lt == .Int && rt == .Int
  then some .Int
  else none
| .Lam s τ body => do
  let τ' ← infer (HashMap.insert ctx (.Var s) τ) body
  some (.Arrow τ τ')
| .App fn arg => do
  let τ ← infer ctx fn
  let τ' ← infer ctx arg
  match τ with
  | .Arrow arg ret => if arg == τ' then some ret else none
  | _ => none
| .Unit => some .Unit

def typecheck : (judgement : Judgement) → Bool
| .Judgement ctx exp ty => infer ctx exp == some ty

end Impl1

-- impl 2 --

namespace IndProp

inductive has_type : Γ → Exp → Ty → Type where
| TInt  :
   ∀ Γ
   , has_type Γ (.Num n) .Int

| TUnit :
    ∀ Γ
    , has_type Γ .Unit .Unit

| TVar :
    ∀ Γ exp τ
    , HashMap.find? Γ exp = some τ
    → has_type Γ exp τ

| TAdd :
    ∀ Γ
    , has_type Γ l .Int
    → has_type Γ r .Int
    → has_type Γ (.Add l r) .Int

| TAbs :
    ∀ Γ nm body τ τ'
    , has_type (HashMap.insert Γ (.Var nm) τ) body τ'
    → has_type Γ (.Lam nm τ body) (.Arrow τ τ')

| TApp :
    ∀ Γ fn arg τ τ'
    , has_type Γ fn (.Arrow τ τ')
    → has_type Γ arg τ
    → has_type Γ (.App fn arg) τ'

inductive well_typed : Γ → Exp → Ty → Prop where
| well_typed : has_type ctx e τ → well_typed ctx e τ

theorem add104 : well_typed ctx (.Add (.Num 10) (.Num 4)) .Int := .well_typed (.TAdd ctx (.TInt ctx) (.TInt ctx))

def format_proof : has_type ctx e τ → String
| .TInt _ => ".TInt"
| _ => sorry

-- traverses `exp` and checks if it is of type `τ` under `ctx`. returns evidence of this judgement if it holds.
def typecheck (ctx : Γ) : (exp : Exp) → (τ : Ty) → Option (has_type ctx exp τ)
| .Unit, .Unit => some (.TUnit ctx)
| .Num _, .Int => some (.TInt ctx)
| .Add l r, .Int => do
    let lj ← typecheck ctx l .Int
    let rj ← typecheck ctx r .Int
    some (.TAdd ctx lj rj)
| .Var s, τ =>
    if h : HashMap.find? ctx (.Var s) == some τ
    then some (.TVar ctx (.Var s) τ (by apply eq_of_beq; assumption))
    else none
| .Lam arg ty body, .Arrow x y =>
    if h : x == ty
    then do
      let sub ← typecheck (HashMap.insert ctx (.Var arg) ty) body y
      have : x = ty := by apply eq_of_beq; assumption
      pure (this ▸ (.TAbs ctx arg body ty y sub))
    else none
-- TODO: need to infer here?
| .App l r, _  => sorry
| _, _=> none


-- TODO: lexi homework
/- def typecheck (ctx : Γ) (exp : Exp) (ty: Ty) : (Option (has_type ctx exp ty)) := sorry -/

end IndProp

end STLC
