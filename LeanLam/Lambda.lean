import Lean

-- the lambda calculus
namespace Lambda

-- de bruijn indexed lambda terms
inductive Exp
| Var : Nat → Exp
| Lam : Exp → Exp
| App : Exp → Exp → Exp
deriving Repr, BEq

namespace Exp

declare_syntax_cat lam
syntax num      : lam
syntax term     : lam
syntax lam lam  : lam
syntax "λ." lam : lam
syntax " ( " lam " ) " : lam -- bracketed expressions

-- Auxiliary notation for translating `arith` into `term`
syntax " ⟪ " lam " ⟫ " : term


-- Our macro rules perform the "obvious" translation:
macro_rules
  | `(⟪ $num:num ⟫)       => `(Var $num)
  | `(⟪ $t:term ⟫)        => `($t)
  | `(⟪ $x:lam $y:lam ⟫)  => `(App ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ λ.$x:lam ⟫)       => `(Lam ⟪ $x ⟫)
  | `(⟪ ( $x:lam ) ⟫)     => `( ⟪ $x ⟫ )

def formatExp : (e : Exp) → Std.Format
| Var i    => repr i
| App f a  => "(" ++ (formatExp f) ++ " " ++ (formatExp a) ++ ")"
| Lam b    => "λ." ++ formatExp b


-- inductive Sub
-- | Inc : Nat → Sub
-- | Extend : Exp → Sub → Sub
-- | Compose : Sub → Sub → Sub
--
-- def lift (s : Sub) : Sub := Sub.Extend (Var 0) (Sub.Compose s (Sub.Inc 1))
--
-- mutual
--
-- partial def apply : Sub → Nat → Exp
--   | (Sub.Inc k), x => Var (k + x)
--   | (Sub.Extend x _), 0 => x
--   | (Sub.Extend _ s), (x + 1) => apply s x
--   | (Sub.Compose s1 s2), x => subst s1 (apply s1 x)
--
-- partial def subst (s : Sub) (e : Exp) : Exp :=
--   match e with
--   | Var i => apply s i
--   | App e1 e2 => App (subst s e1) (subst s e2)
--   | Lam e => Lam (subst (lift s) e)
--
-- end


/-
In the β-reduction (λ M) N, for example, we must

1. find the instances of the variables n1, n2, ..., nk in M that are bound by the λ in λ M,

2. decrement the free variables of M to match the removal of the outer λ-binder, and

3. replace n1, n2, ..., nk with N, suitably incrementing the free variables occurring in N each time, to match the number of λ-binders, under which the corresponding variable occurs when N substitutes for one of the ni.
-/

def incrementFree (e : Exp) (incBy : Nat) (depth : Nat) : Exp := match e with
| Var i => if i ≥ depth then Var (i + incBy) else Var i
| App f a => App (incrementFree f incBy depth) (incrementFree a incBy depth)
| Lam body => Lam (incrementFree body incBy (depth + 1))


def subst (target : Exp) (depth : Nat) (arg : Exp) : Exp :=
  match target with
  | Var idx =>
      if idx == depth then (incrementFree arg depth 0)
      else if idx > depth then Var (idx - 1) -- decrement because we stripped a lambda
      else Var idx
  | Lam body => Lam (subst body (depth + 1) arg)
  | App f a => App (subst f depth arg) (subst a depth arg)

partial def βreduce : (e : Exp) → Exp
| App (Lam body) arg => βreduce $ subst body 0 arg
| App a b => App (βreduce a) (βreduce b)
| Lam body => Lam $ βreduce body
| Var n => Var n

def reduceN : (e : Exp) → (fuel : Nat) → Exp
| e, 0 => e
| e, n + 1 =>
  let y := βreduce e
  dbg_trace ("fuel: " ++ repr (n + 1) ++ " val: " ++ formatExp y)
  if y == e then e else reduceN y n

def y := ⟪λ.(λ. 1 (0 0)) (λ. 1 (0 0)) ⟫
#eval (formatExp (reduceN (App y (Var 5)) 4))
#eval formatExp $ βreduce ⟪ (λ.λ.0 1) 0⟫
#reduce ⟪ λ.λ.0 1 ⟫


end Exp
end Lambda
