import Lean

-- the lambda calculus
namespace DeBruijn

-- de bruijn indexed lambda terms
inductive Exp
| Var : Nat → Exp
| Lam : Exp → Exp
| App : Exp → Exp → Exp
deriving Repr, BEq

namespace Exp

declare_syntax_cat lam
syntax num      : lam
syntax ident    : lam
syntax lam lam  : lam
syntax "λ." lam : lam
syntax " ( " lam " ) " : lam -- bracketed expressions

-- Auxiliary notation for translating `lam` into `term`
syntax " ⟪ " lam " ⟫ " : term

macro_rules
  | `(⟪ $num:num ⟫)      => `(Var $num)
  | `(⟪ $i:ident ⟫)      => `($i)
  | `(⟪ $x:lam $y:lam ⟫) => `(App ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ λ.$x:lam ⟫)      => `(Lam ⟪ $x ⟫)
  | `(⟪ ( $x:lam ) ⟫)    => `(⟪ $x ⟫)

def formatExp : (e : Exp) → Std.Format
| Var i   => repr i
| App f a => "(" ++ (formatExp f) ++ " " ++ (formatExp a) ++ ")"
| Lam b   => "λ." ++ formatExp b


/-
In the β-reduction (λ M) N, for example, we must

1. find the instances of the variables n1, n2, ..., nk in M that are bound by the λ in λ M,

2. decrement the free variables of M to match the removal of the outer λ-binder, and

3. replace n1, n2, ..., nk with N, suitably incrementing the free variables occurring in N each time, to match the number of λ-binders, under which the corresponding variable occurs when N substitutes for one of the ni.
-/

-- Compute the β-normal form of the input (if it exists).
-- This uses normal order evaluation (a.k.a lazy).
def β : Nat → Exp → Exp
| 0, e => e
| n + 1, e => match e with
  | App (Lam body) arg => β n (subst body 0 arg)
  | App a b =>
    let r := β n a
    if r != a
    -- if β changed a then we start again
    then β n (App r b)
    -- otherwise continnue to b
    else App a (β n b)
  | Lam body => Lam (β n body)
  | Var n => Var n
where
  subst (target : Exp) (depth : Nat) (arg : Exp) : Exp :=
    match target with
    | Var idx =>
        if idx == depth then (incrementFree arg depth 0)
        else if idx > depth then Var (idx - 1) -- decrement because we stripped a lambda
        else Var idx
    | Lam body => Lam (subst body (depth + 1) arg)
    | App f a => App (subst f depth arg) (subst a depth arg)

  incrementFree (e : Exp) (incBy : Nat) (depth : Nat) : Exp := match e with
  | Var i => if i ≥ depth then Var (i + incBy) else Var i
  | App f a => App (incrementFree f incBy depth) (incrementFree a incBy depth)
  | Lam body => Lam (incrementFree body incBy (depth + 1))


-- booleans
def true := ⟪ λ.λ.1 ⟫
def false := ⟪ λ.λ.0 ⟫
def ite := ⟪ λ.λ.λ.2 1 0 ⟫

-- numbers
def zero := ⟪ λ.λ.0 ⟫
def one := ⟪ λ.λ.1 0 ⟫
def two := ⟪ λ.λ.1 (1 0) ⟫
def succ := ⟪ λ.λ.λ. 1 (2 1 0) ⟫

def add := ⟪ λ.λ.1 succ 0 ⟫


def y := ⟪ λ.(λ. 1 (0 0)) (λ. 1 (0 0)) ⟫
#eval formatExp $ β 10 ⟪ (λ.λ.0 1) 0⟫
#reduce ⟪ λ.λ.0 1 ⟫
#eval (formatExp (β 10 (⟪y 5⟫)))
#eval (⟪ y 5 ⟫)


end Exp
end DeBruijn
