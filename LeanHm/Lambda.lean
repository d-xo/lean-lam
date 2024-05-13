import Lean

-- the lambda calculus
namespace Lambda

-- de bruijn indexed lambda terms
inductive Exp
| Var : Nat → Exp
| Lam : Exp → Exp
| App : Exp → Exp → Exp

namespace Exp

inductive Sub
| Inc : Nat → Sub
| Extend : Exp → Sub → Sub
| Compose : Sub → Sub → Sub

def lift (s : Sub) : Sub := Sub.Extend (Var 0) (Sub.Compose s (Sub.Inc 1))

mutual

partial def apply : Sub → Nat → Exp
  | (Sub.Inc k), x => Var (k + x)
  | (Sub.Extend x _), 0 => x
  | (Sub.Extend _ s), (x + 1) => apply s x
  | (Sub.Compose s1 s2), x => subst s1 (apply s1 x)

partial def subst (s : Sub) (e : Exp) : Exp :=
  match e with
  | Var i => apply s i
  | App e1 e2 => App (subst s e1) (subst s e2)
  | Lam e => Lam (subst (lift s) e)

end


def βreduce (e : Exp) : Exp :=
  match e with
  | App (Lam body) arg =>
    -- decrement free in body
    -- sub arg into body & increment free in arg
    sorry
  | App a b => App (βreduce a) (βreduce b)
  | Lam body => Lam (βreduce body)
  | Var n => Var n


end Exp
end Lambda
