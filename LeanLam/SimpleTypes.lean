-- The simply typed lambda calculus

import Lean.Data.HashMap
open Lean

namespace STLC

inductive Ty where
| Int : Ty
| Unit : Ty
| Arrow : Ty → Ty → Ty
deriving BEq, Hashable

inductive Exp where
| Var : String → Exp
| Lam : String → Ty → Exp → Exp
| App : Exp → Exp → Exp
| Num : Int → Exp
| Add : Exp → Exp → Exp
| Unit : Exp
deriving BEq, Hashable

abbrev Γ := Lean.HashMap Exp Ty

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

inductive Judge : Γ → Exp → Ty → Type u where
| TInt : Judge ctx (.Num n) (.Int)
| TUnit : Judge ctx .Unit .Unit
| TAdd (_ : Judge ctx l .Int) (_ : Judge ctx r .Int) : Judge ctx (.Add l r) .Int
| TAbs (_ : Judge (HashMap.insert ctx (.Var s) τ) body τ') : Judge ctx (.Lam nm τ body) (.Arrow τ τ')
| TApp (_ : Judge ctx fn (.Arrow τ ret)) (_ : Judge ctx arg τ) : Judge ctx (.App fn arg) ret

theorem add104 : Judge empty (.Add (.Num 10) (.Num 4)) .Int := .TAdd .TInt .TInt

end STLC
