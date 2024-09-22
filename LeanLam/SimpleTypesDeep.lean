
import Lean.Data.HashMap
open Lean

namespace deeep

inductive Ty where
| Int : Ty
| Unit : Ty
| Arrow : Ty → Ty → Ty
| Var : String → Ty
deriving Repr, BEq, DecidableEq, Hashable

def Ty.format: Ty -> String
    | Ty.Int => "int"
    | Ty.Unit => "unit"
    | Ty.Var name => s!"{name}"
    | Ty.Arrow a b => s!"{Ty.format a}->{Ty.format b}"

instance: ToString Ty where
  toString := Ty.format

def tyVar : Ty := Ty.Var "omg"
def tyInt : Ty := Ty.Int
def tyUnit : Ty := Ty.Unit
def tyArrow : Ty := Ty.Arrow tyInt tyUnit
def tyArrow_ : Ty := Ty.Arrow tyInt tyInt
def tyArrow__ : Ty := Ty.Arrow tyVar tyInt

inductive Exp where
| Var : String → Exp
| Lam : String → Ty → Exp → Exp
| App : Exp → Exp → Exp
| Num : Int → Exp
| Add : Exp → Exp → Exp
| Unit : Exp
deriving Repr, BEq, Hashable

def Exp.format: Exp -> String
  | Var name => s!"{name}"
  | Lam var ty exp => s!"λ{var}:{Ty.format ty}.{Exp.format exp}"
  | App a b => s!"{Exp.format a} {Exp.format b}"
  | Num n => s!"{n}"
  | Add a b => s!"{Exp.format a}+{Exp.format b}"
  | Unit => "()"

instance: ToString Exp where
  toString := Exp.format

def expVar : Exp := Exp.Var "var1"
def expNum : Exp := Exp.Num 4
def expAdd : Exp := Exp.Add expVar expNum
def expLam : Exp := Exp.Lam "x" Ty.Int expAdd
def expLam_ : Exp := Exp.Lam "x" Ty.Int (Exp.Add expVar (Exp.Var "x"))
def expApp : Exp := Exp.App expLam expNum
def expApp_ : Exp := Exp.App expLam_ expNum

/- This implementation of structure prevents us to have multiple structural variables. E.g. the following rule is not possible, but with monotonic context its not neccesery, IIRC:

Δ ⊢ e2:τ'
Γ ⊢ e1:τ
--------------------
Γ,Δ ⊢ (e1,e2):(τ×τ')

-/
inductive Structure where
| Empty : Structure
| Var : String → Structure
| Comma : Exp → Ty → Structure → Structure
deriving Repr

def strEmpty : Structure := Structure.Empty
def strVar : Structure := Structure.Var "Γ"
def strComma : Structure := Structure.Comma expNum tyInt strVar
def strComma_ : Structure := Structure.Comma expVar tyInt strVar

structure Sequent where
  ctx : Structure
  exp : Exp
  ty  : Ty

def seq1 : Sequent := {ctx := strComma_, exp := expApp_, ty := tyInt}
def seq2 : Sequent := { 
    ctx := Structure.Var "Γ",
    exp := Exp.App (Exp.Var "e1") (Exp.Var "e2"),
    ty := Ty.Var "τ'"
    }
def seq3 : Sequent := { 
    ctx := Structure.Comma expVar tyVar $ Structure.Var "Γ",
    exp := expVar,
    ty := tyVar
    }
def seq4 : Sequent := { 
    ctx := Structure.Var "Γ",
    exp := expNum,
    ty := tyInt
    }

/- Γ, var1:int ⊢ λx:int.var1+x:τ->int -/
def seqPr1 : Sequent := { 
    ctx := Structure.Var "Γ",
    exp := Exp.Lam "x" Ty.Int (Exp.Add expVar (Exp.Var "x"))
,
    ty := Ty.Arrow tyVar tyInt
    }

/- Γ, var1:int ⊢ 4:τ -/
/- todo -/

structure Rule where
 name : String
 premisses : List Sequent 
 conclusion : Sequent
 check : Option (Sequent -> Bool)

abbrev Calculus := List Rule

/- Substitution is a list of variables that will assign to Exp -/
abbrev Substitution (α : Type) := List (String × α)

def formatAssignment [ToString α] : (String × α) → String := fun (name, exp) => s!"{name} ← {exp}"
def formatAssignments [ToString α] (xs: List (String × α)): List String := xs.map formatAssignment
def formatSubstitution [ToString α] (xs: Substitution α) : String := "; ".intercalate (formatAssignments xs)

def Substitution.format [ToString α]: Substitution α → String := formatSubstitution

instance [ToString α]: ToString (Substitution α) where
  toString s := s!"[{formatSubstitution s}]"

def substVar1 : Substitution Exp := [("var1", Exp.Num 3)]
def substX : Substitution Exp    := [("x", Exp.Num 3)]

#eval s!"{substVar1}"

def Structure.format: Structure -> String
  | Empty => "∅"
  | Var name => s!"{name}"
  | Comma e t Empty => s!"{Exp.format e}:{Ty.format t}"
  | Comma e t (Var name) => s!"{name}, {Exp.format e}:{Ty.format t}"
  | Comma e t c => s!"{Structure.format c}, {Exp.format e}:{Ty.format t}"

instance: ToString Structure where
  toString := Structure.format

def Sequent.format (s:Sequent) : String := s!"{Structure.format s.ctx} ⊢ {Exp.format s.exp}:{Ty.format s.ty}"
instance: ToString Sequent where
toString := Sequent.format

def Rule.format (r:Rule) : String := s!"{String.intercalate "\n" prs}\n{dash}\n{con}"
  where
    prs := r.premisses.map (fun p => Sequent.format p)
    con := Sequent.format r.conclusion
    longest := (prs.concat con).foldl (fun a str => if a > str.length then a else str.length) 0
    dash := s!"{String.mk (List.replicate longest '-')} {r.name}"

instance: ToString Rule where
toString r : String := Rule.format r

instance: Repr Rule where
  reprPrec := fun rule _ => Rule.format rule

def Calculus.format (rules : List Rule) : String := String.intercalate "\n\n" $ rules.map Rule.format


def unitRule : Rule := { 
  name := "Unit",
  premisses := [],
  conclusion := { 
    ctx := Structure.Var "Γ",
    exp := Exp.Unit,
    ty := Ty.Unit 
    },
  check := none
  }

def varRule : Rule := { 
  name := "Var",
  premisses := [],
  conclusion := { 
    ctx := Structure.Comma (Exp.Var "x") (Ty.Var "τ") (Structure.Var "Γ")
    exp := Exp.Var "x",
    ty := Ty.Var "τ"
    },
   check := some fun s:Sequent => match s.exp with  /- rename to precompile and see whats up? -/
    | Exp.Var _ => True
    | _ => False
  }

/- This needs to be checked by the theorem prover, weird implementation -/
def intRule : Rule := { 
  name := "Int",
  premisses := [],
  conclusion := { 
    ctx := Structure.Var "Γ",
    exp := Exp.Var "n",
    ty := Ty.Int
    },
   check := some fun s:Sequent => match s.exp with  /- rename to precompile and see whats up? -/
    | Exp.Num _ => True
    | _ => False
  }

def addRule: Rule := { 
  name := "Num",
  premisses := [
    {
      ctx := Structure.Var "Γ",
      exp := Exp.Var "a",
      ty  := Ty.Int
    },
    {
      ctx := Structure.Var "Γ",
      exp := Exp.Var "b",
      ty  := Ty.Int
    }
  ],
  conclusion := { 
    ctx := Structure.Var "Γ",
    exp := Exp.Add (Exp.Var "a") (Exp.Var "b"),
    ty := Ty.Int
    },
   check := none
  }

def absRule: Rule := { 
  name := "Abs",
  premisses := [
    {
      ctx := Structure.Comma (Exp.Var "x") (Ty.Var "τ") (Structure.Var "Γ")
      exp := Exp.Var "e",
      ty  := Ty.Var "τ'"
    }
  ],
  conclusion := { 
    ctx := Structure.Var "Γ",
    exp := Exp.Lam "x" (Ty.Var "τ") (Exp.Var "e")
    ty := Ty.Arrow (Ty.Var "τ") (Ty.Var "τ'")
    },
   check := none
  }


def appRule: Rule := { 
  name := "App",
  premisses := [
    {
      ctx := Structure.Var "Γ",
      exp := Exp.Var "e1",
      ty  := Ty.Arrow (Ty.Var "τ") (Ty.Var "τ'")
    },
    {
      ctx := Structure.Var "Γ",
      exp := Exp.Var "e2",
      ty  := Ty.Var "τ"
    }
  ],
  conclusion := { 
    ctx := Structure.Var "Γ",
    exp := Exp.App (Exp.Var "e1") (Exp.Var "e2"),
    ty := Ty.Var "τ'"
    },
   check := none
  }

def simpleTypedLampdaCalculus : Calculus := [
  varRule,
  intRule,
  unitRule,
  absRule,
  appRule,
  addRule
]

def substituteTy (s:Substitution Ty) : Ty → Ty
|Ty.Var name => match (s.findSome? (fun p => if p.1 == name then some p.2 else none)) with
  |some e => e 
  |none => .Var name
|Ty.Int => Ty.Int
|Ty.Unit => Ty.Unit
|Ty.Arrow t1 t2 => Ty.Arrow (substituteTy s t1) (substituteTy s t2)

def matchTy: Ty → Ty → Option (Substitution Ty)
|Ty.Var name, b => some [(name, b)]
|Ty.Int, Ty.Int => some []
|Ty.Unit, Ty.Unit => some []
|Ty.Arrow t11 t12, Ty.Arrow t21 t22 => do
  let σ1 ← matchTy t11 t21
  let σ2 ← matchTy t12 t22
  return σ1 ++ σ2
|_, _ => none

#eval matchTy tyInt tyInt
#eval matchTy tyVar tyInt
#eval matchTy tyArrow tyArrow_
#eval matchTy tyArrow_ tyArrow
#eval matchTy tyArrow__ tyArrow_
#eval matchTy tyArrow_ tyArrow__

def substituteExp (s:Substitution Exp): Exp → Exp
|.Var name => match (s.findSome? (fun p => if p.1 == name then some p.2 else none)) with
  |some e => e 
  |none => .Var name
|.Unit => .Unit
|.Num n => .Num n
|.Lam name ty exp => .Lam name ty (substituteExp (s.filter (·.1 != name)) exp)
|.App exp1 exp2 => .App (substituteExp s exp1) (substituteExp s exp2)
|.Add exp1 exp2 => .Add (substituteExp s exp1) (substituteExp s exp2)


#eval Exp.format expLam_
#eval Exp.format expLam
#eval Exp.format $ substituteExp substX expLam_
#eval Exp.format $ substituteExp substX expLam
#eval Exp.format $ substituteExp substVar1 expLam_
#eval Exp.format $ substituteExp substVar1 expLam

/- 
  todo: current Idea: matchExp needs also to mach Ty since expressions contain types
-/
def matchExp: Exp → Exp → Option (Substitution Exp)
|Exp.Var name, b => some [(name, b)]
|Exp.Lam name ty exp, Exp.Lam name2 ty2 exp2 => 
  /- todo: name is subject to debrujinification?, ty is subject to matching -/
  if name == name2 && ty == ty2 
  /- match should omit bound variables in the lambda case -/
  then (matchExp exp exp2).map (·.filter (·.1 != name))
  else none
|Exp.App exp11 exp12, Exp.App exp21 exp22 => do
  let σ1 ← matchExp exp11 exp21
  let σ2 ← matchExp exp12 exp22
  return σ1 ++ σ2
|Exp.Num n, Exp.Num m => if n == m then some [] else none
|Exp.Add exp11 exp12, Exp.Add exp21 exp22 => do
  let σ1 ← matchExp exp11 exp21
  let σ2 ← matchExp exp12 exp22
  return σ1 ++ σ2
|Exp.Unit, Exp.Unit => some []
|_, Exp.Var name => some []
|_, _ => none

#eval matchExp expNum expAdd
#eval matchExp expNum expNum
#eval matchExp expVar expVar
#eval Exp.format expApp
#eval Exp.format expApp_
#eval matchExp expApp expApp_
#eval matchExp expApp_ expApp
#eval matchExp expVar expApp
  

def propagateSubstitution (σExp: Substitution Exp)  (σTy: Substitution Ty) : Structure → Structure
|.Var name => .Var name
|.Empty => .Empty
|.Comma exp ty str => .Comma (substituteExp σExp exp) (substituteTy σTy ty) (propagateSubstitution σExp σTy str)

def substituteStructure (s: Substitution Structure) : Structure → Structure
|.Var name => match (s.findSome? (fun p => if p.1 == name then some p.2 else none)) with
  |some e => e 
  |none => .Var name
|.Empty => .Empty
|.Comma exp ty str => .Comma exp ty (substituteStructure s str)

def matchStructure: Structure → Structure → Option (Substitution Structure)
|.Var name, b => some [(name, b)]
|.Empty, .Empty => some []
/- TODO: here order should not matter, construct hash map and check for subset -/
|.Comma _ _ _, .Comma _ _ _ => some []
|_, _ => none

#eval matchStructure strVar strComma
#eval matchStructure strComma strComma

structure SeqSubstitution where
  Exp: Substitution Exp
  Ty: Substitution Ty
  Str: Substitution Structure
deriving Repr

instance: ToString SeqSubstitution where
  toString s := s!"Exp{s.Exp} Ty{s.Ty} Str{s.Str}"

def matchSeq (a: Sequent) (b: Sequent) : Option SeqSubstitution := do
  let σExp ← matchExp a.exp b.exp
  let σTy ← matchTy a.ty b.ty
  let σStr ← matchStructure a.ctx (propagateSubstitution σExp σTy b.ctx)
  return {Exp := σExp, Ty := σTy, Str := σStr}

def substituteSeq (σ:SeqSubstitution) (s:Sequent): Sequent := { 
  ctx := substituteStructure σ.Str s.ctx,
  exp := substituteExp σ.Exp s.exp,
  ty := substituteTy σ.Ty s.ty
  }

def matchRule (a:Sequent) (r:Rule) : Option SeqSubstitution := do
  if match r.check with
  |some f => f a 
  |none => true
  then matchSeq r.conclusion a
  else none

#eval Sequent.format seq1
#eval Sequent.format seq2
#eval Sequent.format seq3
#eval matchSeq seq2 seq1
def σResult := match (matchSeq seq2 seq1) with
|some p => p
|none => {Exp := [], Ty := [], Str := []}
#eval Sequent.format $ substituteSeq σResult seq2
#eval matchSeq seq3 seq1
#eval varRule.check <*> (some seq1)
#eval varRule.check <*> (some seq2)
#eval varRule.check <*> (some seq3)
#eval intRule.check <*> (some seq1)
#eval intRule.check <*> (some seq2)
#eval intRule.check <*> (some seq3)
#eval intRule.check <*> (some seq4)


/-
  What i try to do: Sequent -> Option ProofNode
  have: conclusion
  1. get pot rules `ruleSelection : Sequent -> List (σ × Rules)`
  2. each rule until success `findSome` `List Rules -> Option ProofNode`
    have r:Rule
    3. get sigma 
    4. apply sigma to premisses
    5. each premisse untill failture: 
      recurse
-/

inductive ProofTree where
| Open : Sequent → ProofTree
| Leaf : Sequent → Rule → ProofTree
| Node : Sequent → Rule → SeqSubstitution → List Sequent → List ProofTree → ProofTree
| Failed : Sequent → ProofTree

partial def ProofTree.format: ProofTree → String
  | .Open s => s!"open {s}"
  | .Leaf s r => s!"leaf '{s}' with {r.name}"
  | .Node s r σ ps ts => s!"node '{s}' with {r.name} σ[{σ}] ps[{ps}] ({ts.map ProofTree.format})"
  | .Failed s => s!"failed '{s}'"

instance: Repr ProofTree where
  reprPrec := fun pt _ => ProofTree.format pt

def ruleSelection (seq: Sequent): List (SeqSubstitution × Rule) := 
simpleTypedLampdaCalculus.filterMap (fun rule => (matchRule seq rule ).map (·, rule))

/- todo: better name -/
def getPremisses: (SeqSubstitution × Rule) → Option (List Sequent) := 
(fun (σ, rule) => some $ rule.premisses.map (substituteSeq σ ·) )

/- todo -/
mutual

partial def tryRule (s:Sequent) (p:SeqSubstitution × Rule) : Option ProofTree := do
  let ps <- getPremisses p
  let nodes <- ps.mapM prove
  if nodes.length > 0 
  then ProofTree.Node s p.2 p.1 ps nodes
  else ProofTree.Leaf s p.2


partial def prove (s:Sequent) : Option ProofTree :=
  match (ruleSelection s).findSome? (tryRule s) with
  | some pt => pt
  | none => ProofTree.Failed s
end


#eval prove seq1

/-                                    Γ ⊢ λx:τ.e:τ->τ' -/
#eval prove seqPr1

#eval matchExp (Exp.Lam "x" (Ty.Var "τ") (Exp.Var "e")) (Exp.Lam "x" Ty.Int (Exp.Add expVar (Exp.Var "x")))
 
/- 

some 
  node 'Γ, var1:int ⊢ λx:int.var1+x 4:int' with App 
  σ[
    Exp[
      e1 ← λx:int.var1+x;
      e2 ← 4] 
    Ty[
      τ' ← int] 
    Str[
      Γ ← Γ, 
      var1:int
      ]]
  ps[[
    Γ, var1:int ⊢ λx:int.var1+x:τ->int
    Γ, var1:int ⊢ 4:τ
    ]]
  ([failed 'Γ, var1:int ⊢ λx:int.var1+x:τ->int', failed 'Γ, var1:int ⊢ 4:τ'])

-/


/- def bla (r:Rule) (σ:SeqSubstitution) : Option (SeqSubstitution × Rule) := some (σ, r) -/

/- 
test all the rules in the calculus for application
returns all possible rules
-/

/- 
gets a potential rule to apply
applies the substitution to the premisses and returns a 
-/

/- def possibleRulesSeq1 : List (SeqSubstitution × Rule) := ruleSelection seq1 -/
/- #eval (possibleRulesSeq1.findSome? propageteProofState) -/
/- /- I want `List a -> (a -> Option b) -> Option List b  -/ -/
/- def what := possibleRulesSeq1.mapM propageteProofState -/
/- #eval what -/
/- def prove  (s:Sequent) (c:Calculus) : Option Bool := -/
/-   let x := c.map matchSeq -/


end deeep

open deeep

def main : IO Unit := do
  IO.println (Calculus.format simpleTypedLampdaCalculus)
