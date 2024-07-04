import Lean

-- the lambda calculus
namespace Named

open Lean
open Lean.Parser
open Meta

-- de bruijn indexed lambda terms
inductive Exp
| Var : String → Exp
| Lam : String → Exp → Exp
| App : Exp → Exp → Exp
deriving Repr, BEq

namespace Exp

declare_syntax_cat lam_nm
syntax str             : lam_nm
syntax ident           : lam_nm
syntax lam_nm lam_nm         : lam_nm
syntax "λ" str "." lam_nm : lam_nm
syntax " ( " lam_nm " ) " : lam_nm -- bracketed expressions

-- Auxiliary notation for translating `lam_nm` into `term`
syntax " ⟪ " lam_nm " ⟫ " : term

macro_rules
  | `(⟪ $i:ident ⟫)       => `($i)
  | `(⟪ $n:str ⟫)         => `(Var $n)
  | `(⟪ $x:lam_nm $y:lam_nm ⟫)  => `(App ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ λ$s:str.$x:lam_nm ⟫) => `(Lam $s ⟪ $x ⟫)
  | `(⟪ ( $x:lam_nm ) ⟫)     => `(⟪ $x ⟫)

def formatExp : (e : Exp) → Std.Format
| Var i   => i
| App f a => "(" ++ (formatExp f) ++ " " ++ (formatExp a) ++ ")"
| Lam s b   => "(λ" ++ s ++ "." ++ formatExp b ++ ")"

#eval formatExp ⟪ λ"x".λ"y"."z" ⟫

-- rename all references to `before` in `exp` to refer to `after`
-- INVARIANT: `after` must be fresh in all scopes contained in `exp`
def rename (exp : Exp) (before : String) (after : String) := match exp with
| Var nm => if nm == before then Var after else Var nm
| App a b => App (rename a before after) (rename b before after)
| Lam nm body =>
  if nm == before
  -- if nm == before then it is rebound in body and we don't rename further
  then Lam nm body
  -- we assume that `after` is always fresh in all scopes, so we can safely
  -- rename in body without further checks
  else Lam nm (rename body before after)

-- custom termination metric for `subst`. this is just the default `sizeOf` that
-- leans generates, but we ignore the size of strings (since these can be
-- modified by capture avoiding subsition, but are not iterated over during substitution)
def depth : (e : Exp) → Nat
| Var _ => 1
| App a b => 1 + depth a + depth b
| Lam _ b => 1 + depth b

-- the depth of a renamed term is the same as the depth of the original term
theorem depth_rename α β γ : depth (rename α β γ) = depth α := by
  induction α with
  | Var n =>
      simp [depth, rename]
      split
      · simp [depth]
      · simp [depth]
  | App n m ihn ihm => simp [depth, ihn, ihm]
  | Lam n m ihm =>
      simp [depth, rename]
      split
      · simp [depth]
      · simp [depth, ihm]

def subst (target : Exp) (var : String) (arg : Exp) : Exp :=
  match target with
  | Var nm => if nm == var then arg else Var nm
  | App α β =>
      -- termination
      have : depth α < depth (App α β) := by
        simp [depth]


        /- , Nat.lt_add_right, Nat.lt_add_of_pos_left] -/
        refine Nat.lt_add_right (depth β) ?h

        apply?
      have : depth β < depth (App α β) := by simp [depth, Nat.lt_add_right, Nat.lt_add_of_pos_left]
      -- recurse
      App (subst α var arg) (subst β var arg)
  | Lam nm body =>
      -- do we need to rename (to avoid capture)
      if nm == var || freeIn arg nm
      then
        -- generate a fresh name
        let fresh := genFresh arg body var
        -- replace all references to `nm` in `body` to `fresh`
        let renamed := rename body nm fresh

        -- termination
        have : depth renamed < depth (Lam nm body) := by
          simp [depth, renamed, depth_rename, Nat.lt_add_of_pos_left]

        -- substitute references to `var` with `renamed` in the body
        Lam fresh (subst renamed var arg)

      else
        -- termination
        have : depth body < depth (Lam nm body) := by simp [depth, Nat.lt_add_of_pos_left]
        -- recurse
        Lam nm (subst body var arg)
  termination_by (depth target)
where
  -- gets the numeric suffix from a string if it is of the form
  -- "varX" where X is a Nat
  parseString (str : String) : Nat :=
    if str.startsWith "var"
    then Option.getD (str.drop 3).toNat? 0
    else 0

  -- finds the highest suffix of all variables of the form "varX" in `arg`
  findHighestIdx : (arg : Exp) → Nat
  | Var s => parseString s
  | App a b => max (findHighestIdx a) (findHighestIdx b)
  | Lam nm body => max (parseString nm) (findHighestIdx body)

  -- generates a name that:
  --  1. is not the same as `var`
  --  2. is not free in `arg`
  --  3. is not free in `body`
  genFresh (arg : Exp) (body : Exp) (var : String) : String :=
    let idx := max (parseString var)
                   (max (findHighestIdx arg)
                        (findHighestIdx body))
    "var" ++ (toString (idx + 1))

  -- traverses `exp` and checks if `nm` is a free variable
  freeIn (exp : Exp) (nm : String) : Bool := match exp with
  | Var b => nm == b
  | App a b => freeIn a nm || freeIn b nm
  | Lam arg body =>
      if nm == arg
      then False
      else freeIn body nm


def β : Nat → Exp → Exp
| 0, e => e
| n + 1, e => match e with
  | App (Lam var body) arg => β n (subst body var arg)
  | App a b =>
    let r := β n a
    if r != a
    -- if β changed a then we start again
    then β n (App r b)
    -- otherwise continnue to b
    else App a (β n b)
  | Lam var body => Lam var (β n body)
  | Var n => Var n

def y := ⟪ λ"f". (λ"x". "f" ("x" "x")) (λ "x". "f" ("x" "x")) ⟫
#eval (formatExp (β 10 (⟪y "z"⟫)))
#eval (formatExp (β 50 (⟪y (λ"y" . "y")⟫)))

end Exp
end Named
