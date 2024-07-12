-- The simply typed lambda calculus
-- https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus#Typing_rules

import Lean.Data.HashMap
import Aesop
open Lean

namespace STLC

-- Type Specifications --

inductive Ty where
| Int : Ty
| Unit : Ty
| Arrow : Ty → Ty → Ty
deriving DecidableEq, Hashable

-- TODO: why can't I just use the LawfulBEq instance here:
-- https://github.com/leanprover/lean4/blob/8f9843a4a5fe1b0c2f24c74097f296e2818771ee/src/Init/Core.lean#L635C1-L637C37
protected def beq : Ty → Ty → Bool
| .Int, .Int => true
| .Unit, .Unit => true
| .Arrow fn1 arg1, .Arrow fn2 arg2 => STLC.beq fn1 fn2 && STLC.beq arg1 arg2
| _, _ => false

instance : BEq Ty := ⟨STLC.beq⟩

instance : LawfulBEq Ty where
  rfl {a} := by
    induction a with
    | Int => rfl
    | Unit => rfl
    | Arrow τ τ' ihτ ihτ' =>
        simp [BEq.beq, STLC.beq] at *
        apply And.intro <;> assumption
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
      cases b with
      | Unit =>
          simp [ihx, ihy]
          exact rfl
      | Int =>
          simp [ihx, ihy]
          exact rfl
      | Arrow m n =>
          simp [BEq.beq, STLC.beq, ihx, ihy] at *
          intros h h'
          apply And.intro
          · apply (ihx h)
          · apply (ihy h')

-- Expressions --

inductive Exp where
| Var : String → Exp
| Lam : String → Ty → Exp → Exp
| App : Exp → Exp → Exp
| Num : Int → Exp
| Add : Exp → Exp → Exp
| Unit : Exp
deriving BEq, Hashable

-- Typing Context --

abbrev Γ := Lean.HashMap Exp Ty

-- Type Inference --

-- TODO: can this be made to return a `has_type` judgement?
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

-- Shallow Embedding of Typing Rules --

namespace Shallow

-- Typing Judgements --

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

-- Embed Typing Judgements into Prop --

inductive well_typed : Γ → Exp → Ty → Prop where
| well_typed : has_type ctx e τ → well_typed ctx e τ


-- Typechecking --

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
| .App fn arg, τ => do
    -- infer a type for the argument
    let argTy ← infer ctx arg
    -- produce evidence that the infered type is correct
    -- TODO: inefficient to traverse twice here...
    let argJudge ← typecheck ctx arg argTy
    let fnJudge ← typecheck ctx fn (.Arrow argTy τ)
    some (.TApp ctx fn arg argTy τ fnJudge argJudge)
| _, _=> none

end Shallow

-- Deep Embedding of Typing Rules --

-- TODO: denis!
namespace Deep
end Deep

end STLC
