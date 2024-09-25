/-

0. substitution
  - definition
  - format
1. types
  - definition
  - format
  - substitution
  - examples
2. expressions
  - definition
  - format
  - substitution
  - match
  - typecheck
  - examples
3. structures
  - definition
  - format
  - substitute
  - propagate
  - match
  - examples
4. sequent
  - definition
  - format
  - match
  - substitute
5. rule
  - definition
  - format
  - match
  - select
  - substitutePremisses
6. calculus
  - definition
  - format
7. proof
  - definition
  - format
  - prove & byRule
  
TODO: The most problems are still with substitution, debrujinification etc. transitive substitution needs to propagated (e.g. [x <- y, y <- z] => [x <- z, y <- z]), investigate if boud names in the lambda case need to be substituted in a match. They certainly need to be debrujinified. Also potential consistency checks need to be performed.
Another problem I'm aware of is with Structures and their matching, currently order matters which it shouldn't and for more then one typing literal in the structure (l.h.s of the sequent) Structure.match is not working. lol, fuck.
Additionally, idk if rule 'checks' are the way to go to implement 'Var' and 'Int' rules as well as type inference needs to happen for the 'App' rule which seems to be calculus dependend and should not be part of the sequent calculus IMO.

Once this is done, an UltraDeep implementation should be done where parsing plays a central role. Squeeze Exp and Ty into a single literal that is subject to the sequent and on which substitution is performed and abstract matching and substitution to be implementation independent and generated. Which allows quick iterations on rules and literals. etc.

Also a different way to implement structures in general would be nice, since it doesn't allow substructural operations and hence no linear logic. this would be exciting to implement next tho.


-/

import Lean.Data.HashMap
open Lean

namespace deeep


-- 0. substitution

-- definition
-- Substitution is a list of variables that will assign to Exp
abbrev Substitution (α : Type) := List (String × α)

-- format
def formatAssignment [ToString α] : (String × α) → String := 
  fun (name, exp) => s!"{name} ← {exp}"
def formatAssignments [ToString α] (xs: List (String × α)): List String :=
  xs.map formatAssignment
def formatSubstitution [ToString α] (xs: Substitution α) : String :=
  "; ".intercalate (formatAssignments xs)

def Substitution.format [ToString α]: Substitution α → String := formatSubstitution

instance [ToString α]: ToString (Substitution α) where
  toString s := s!"[{formatSubstitution s}]"

-- 1. types
-- definition
inductive Ty where
| Int : Ty
| Unit : Ty
| Arrow : Ty → Ty → Ty
| Var : String → Ty
deriving Repr, BEq, DecidableEq, Hashable

--format
def Ty.format: Ty -> String
    | Ty.Int => "int"
    | Ty.Unit => "unit"
    | Ty.Var name => s!"{name}"
    | Ty.Arrow a b => s!"{Ty.format a}->{Ty.format b}"

instance: ToString Ty where
  toString := Ty.format

-- substitute
def Ty.substitute (s:Substitution Ty) : Ty → Ty
|Ty.Var name => match (s.findSome? (fun p => if p.1 == name then some p.2 else none)) with
  |some e => e 
  |none => .Var name
|Ty.Int => Ty.Int
|Ty.Unit => Ty.Unit
|Ty.Arrow t1 t2 => Ty.Arrow (Ty.substitute s t1) (Ty.substitute s t2)


/- def Ty.unify: Ty → Ty → Option (Substitution Ty) -/
/- |.Var name, b => some [(name, b)] -/
/- |a, .Var name => some [(name, a)] -/
/- |.Int, .Int => some [] -/
/- |.Unit, .Unit => some [] -/
/- |.Arrow t11 t12, .Arrow t21 t22 => do -/
/-   let σ1 ← Ty.unify t11 t21 -/
/-   let σ2 ← Ty.unify t12 t22 -/
/-   return σ1 ++ σ2 -/
/- |_, _ => none -/

/- match Ty needs to be unify - it goes both way -/
def Ty.match: Ty → Ty → Option (Substitution Ty)
|Ty.Var name, b => some [(name, b)]
|Ty.Int, Ty.Int => some []
|Ty.Unit, Ty.Unit => some []
|Ty.Arrow t11 t12, Ty.Arrow t21 t22 => do
  let σ1 ← Ty.match t11 t21
  let σ2 ← Ty.match t12 t22
  return σ1 ++ σ2
|_, _ => none

-- examples
def tyVar : Ty := Ty.Var "omg"
def tyInt : Ty := Ty.Int
def tyUnit : Ty := Ty.Unit
def tyArrow : Ty := Ty.Arrow tyInt tyUnit
def tyArrow_ : Ty := Ty.Arrow tyInt tyInt
def tyArrow__ : Ty := Ty.Arrow tyVar tyInt

#eval Ty.match tyInt tyInt
#eval Ty.match tyVar tyInt
#eval Ty.match tyArrow tyArrow_
#eval Ty.match tyArrow_ tyArrow
#eval Ty.match tyArrow__ tyArrow_
#eval Ty.match tyArrow_ tyArrow__




-- 2. expressions

-- definition
inductive Exp where
| Var : String → Exp
| Lam : String → Ty → Exp → Exp
| App : Exp → Exp → Exp
| Num : Int → Exp
| Add : Exp → Exp → Exp
| Unit : Exp
deriving Repr, BEq, Hashable

-- format
def Exp.format: Exp -> String
  | Var name => s!"{name}"
  | Lam var ty exp => s!"λ{var}:{Ty.format ty}.{Exp.format exp}"
  | App a b => s!"{Exp.format a} {Exp.format b}"
  | Num n => s!"{n}"
  | Add a b => s!"{Exp.format a}+{Exp.format b}"
  | Unit => "()"

instance: ToString Exp where
  toString := Exp.format

-- substitution
def Exp.substitute (s:Substitution Exp): Exp → Exp
|.Var name => match (s.findSome? (fun p => if p.1 == name then some p.2 else none)) with
  |some e => e 
  |none => .Var name
|.Unit => .Unit
|.Num n => .Num n
|.Lam name ty exp => .Lam name ty (Exp.substitute (s.filter (·.1 != name)) exp)
|.App exp1 exp2 => .App (Exp.substitute s exp1) (Exp.substitute s exp2)
|.Add exp1 exp2 => .Add (Exp.substitute s exp1) (Exp.substitute s exp2)

-- match
def Exp.match: Exp → Exp → Option ((Substitution Exp) × (Substitution Ty))
  |.Var name, b => some ([(name, b)], {})
  |.Lam name ty exp, .Lam name2 ty2 exp2 => 
    /- TODO: closed names should not mather ffs. They should also be substituted or debrujinified or something -/
    if name == name2
    then do 
    let σTy' <- Ty.match ty ty2
    let (σExp, σTy) <- (Exp.match exp exp2)
    /- TODO: do i need to check wether a var is assigned twice? -/
    (σExp.filter (·.1 != name), σTy ++ σTy')
    else none
  |.App exp11 exp12, .App exp21 exp22 => do
    let σ1 ← Exp.match exp11 exp21
    let σ2 ← Exp.match exp12 exp22
    return (σ1.1 ++ σ2.1, σ1.2 ++ σ2.2)
  |.Num n, .Num m => if n == m then some ([], []) else none
  |.Add exp11 exp12, .Add exp21 exp22 => do
    let σ1 ← Exp.match exp11 exp21
    let σ2 ← Exp.match exp12 exp22
    return (σ1.1 ++ σ2.1, σ1.2 ++ σ2.2)
  |.Unit, .Unit => some ([], [])
  |_, _ => none

/- TODO: debrujinification? -/
def Exp.typecheck: Exp → Option Ty
|.Var _ => some $ .Var "toDebrujinifyThisShit"
|.Lam name ty exp => do
  let type <- Exp.typecheck exp
  return .Arrow ty type
|.App a _ => match Exp.typecheck a with
  |some $ .Var _ => some $ .Var "toDebrujinifyThisShit"
  |some $ .Arrow _ b => some b
  |_ => none
|.Add _ _ => some .Int
|.Num _ => some .Int
|.Unit => some .Unit

-- examples
def expVar : Exp := Exp.Var "var1"
def expNum : Exp := Exp.Num 4
def expAdd : Exp := Exp.Add expVar expNum
def expLam : Exp := Exp.Lam "x" Ty.Int expAdd
def expLam_ : Exp := Exp.Lam "x" Ty.Int (Exp.Add expVar (Exp.Var "x"))
def expApp : Exp := Exp.App expLam expNum
def expApp_ : Exp := Exp.App expLam_ expNum

def substVar1 : Substitution Exp := [("var1", Exp.Num 3)]
def substX : Substitution Exp    := [("x", Exp.Num 3)]


#eval s!"{substVar1}"

#eval Exp.format expApp
#eval Exp.format expApp_
#eval Exp.format expLam_
#eval Exp.format expLam
#eval Exp.format $ Exp.substitute substX expLam_
#eval Exp.format $ Exp.substitute substX expLam
#eval Exp.format $ Exp.substitute substVar1 expLam_
#eval Exp.format $ Exp.substitute substVar1 expLam

#eval expNum.match expAdd
#eval Exp.match expNum expNum
#eval Exp.match expVar expVar
#eval Exp.match expApp expApp_
#eval Exp.match expApp_ expApp
#eval Exp.match expVar expApp




-- 3. structure
-- definition
/- 
note:

This implementation of structure prevents us to have multiple structural variables. E.g. the following rule is not possible, but with monotonic context its not neccesery, IIRC:

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

-- format
def Structure.format: Structure -> String
  | Empty => "∅"
  | Var name => s!"{name}"
  | Comma e t Empty => s!"{Exp.format e}:{Ty.format t}"
  | Comma e t (Var name) => s!"{name}, {Exp.format e}:{Ty.format t}"
  | Comma e t c => s!"{Structure.format c}, {Exp.format e}:{Ty.format t}"

instance: ToString Structure where
  toString := Structure.format

-- substitute
def Structure.substitute (s: Substitution Structure) : Structure → Structure
|.Var name => match (s.findSome? (fun p => if p.1 == name then some p.2 else none)) with
  |some e => e 
  |none => .Var name
|.Empty => .Empty
|.Comma exp ty str => .Comma exp ty (Structure.substitute s str)

def Structure.propagate (σExp: Substitution Exp)  (σTy: Substitution Ty) : Structure → Structure
|.Var name => .Var name
|.Empty => .Empty
|.Comma exp ty str => .Comma (Exp.substitute σExp exp) (Ty.substitute σTy ty) (Structure.propagate σExp σTy str)

-- match
def Structure.match: Structure → Structure → Option (Substitution Structure)
|.Var name, b => some [(name, b)]
|.Empty, .Empty => some []
-- TODO: here order should not matter, construct hash map and check for subset
-- without it, larger proofs won't work
|.Comma _ _ _, .Comma _ _ _ => some []
|_, _ => none

-- examples
def strEmpty : Structure := Structure.Empty
def strVar : Structure := Structure.Var "Γ"
def strComma : Structure := Structure.Comma expNum tyInt strVar
def strComma_ : Structure := Structure.Comma expVar tyInt strVar

#eval Structure.match strVar strComma
#eval Structure.match strComma strComma



-- 4. sequent
-- definition
structure Sequent where
  ctx : Structure
  exp : Exp
  ty  : Ty

-- format
def Sequent.format (s:Sequent) : String := s!"{Structure.format s.ctx} ⊢ {Exp.format s.exp}:{Ty.format s.ty}"
instance: ToString Sequent where
toString := Sequent.format

-- substitute
structure SeqSubstitution where
  Exp: Substitution Exp
  Ty: Substitution Ty
  Str: Substitution Structure
deriving Repr

instance: ToString SeqSubstitution where
  toString s := s!"Exp{s.Exp} Ty{s.Ty} Str{s.Str}"

-- match
def Sequent.match (a: Sequent) (b: Sequent) : Option SeqSubstitution := do
  let (σExp, σTy) ← Exp.match a.exp b.exp
  let σTy' ← Ty.match a.ty b.ty
  -- TODO: consistency check for σTy
  --       either on this level or propagate σTy to Exp.match and do the consistency check there
  let σStr ← Structure.match a.ctx (Structure.propagate σExp σTy b.ctx)
  return {Exp := σExp, Ty := σTy, Str := σStr}

-- substitute
def Sequent.substitute (σ:SeqSubstitution) (s:Sequent): Sequent := { 
  ctx := Structure.substitute σ.Str s.ctx,
  exp := Exp.substitute σ.Exp s.exp,
  ty := Ty.substitute σ.Ty s.ty
  }

-- examples
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
def seqPr2 : Sequent := { 
    ctx := Structure.Comma expVar tyInt $ Structure.Var "Γ",
    exp := Exp.Num 4 
    ty := tyVar
    }
def seqIntC : Sequent := { 
    ctx := Structure.Comma expVar tyInt $  Structure.Var "Γ",
    exp := Exp.Num 3,
    ty := Ty.Var "τ'"
    }


#eval Sequent.format seq1
#eval Sequent.format seq2
#eval Sequent.format seq3
#eval Sequent.match seq2 seq1
def σResult := match (Sequent.match seq2 seq1) with
|some p => p
|none => {Exp := [], Ty := [], Str := []}
#eval Sequent.format $ Sequent.substitute σResult seq2
#eval Sequent.match seq3 seq1




-- 5. rules
-- definition
structure Rule where
 name : String
 premisses : List Sequent 
 conclusion : Sequent
 check : Option (Sequent -> Bool)

-- format
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


-- match
def Rule.match (a:Sequent) (r:Rule) : Option SeqSubstitution := do
  if match r.check with
  |some f => f a 
  |none => true
  then Sequent.match r.conclusion a
  else none

-- substitution (premisses)
def Rule.substitutePremisses (rule : Rule) (σ : SeqSubstitution) : (List Sequent) := 
rule.premisses.map (Sequent.substitute σ ·)

-- select
-- Given a calculus and a Sequent - get all the rules that apply to that sequent and their substitution
def Rule.select (rs: List Rule) (seq: Sequent): List (SeqSubstitution × Rule) := 
rs.filterMap (fun rule => (Rule.match seq rule ).map (·, rule))

-- examples
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

#eval varRule.check <*> (some seq1)
#eval varRule.check <*> (some seq2)
#eval varRule.check <*> (some seq3)
#eval intRule.check <*> (some seq1)
#eval intRule.check <*> (some seq2)
#eval intRule.check <*> (some seq3)
#eval intRule.check <*> (some seq4)

-- 6. calculus
-- definition
abbrev Calculus := List Rule

-- format
def Calculus.format (rules : List Rule) : String := String.intercalate "\n\n" $ rules.map Rule.format

-- example
def simpleTypedLampdaCalculus : Calculus := [
  varRule,
  intRule,
  unitRule,
  absRule,
  appRule,
  addRule
]




-- 7. proof 
-- definition
inductive Proof where
| Qed : Sequent → Rule → Proof
| Node : Sequent → Rule → SeqSubstitution → List Sequent → List Proof → Proof
| Failed : Sequent → Proof

-- format
partial def Proof.format: Proof → String := formatProofTree ""
where 
  breakAll : List String → String := 
    s!"\n".intercalate
  formatProofTree (indent:String) : Proof → String
  | .Qed s r => s!"{indent}qed '{s}' with {r.name}"
  | .Node s r σ ps ts => s!"{indent}proof '{s}' with {r.name} \n│ {indent}σ[{σ}] \n│ {indent}ps {ps.length}[{"; ".intercalate $ ps.map Sequent.format}] \n{breakAll $ ts.map $ formatProofTree (indent ++ "│ ")})"
  | .Failed s => s!"{indent}failed '{s}'"

instance: Repr Proof where
  reprPrec := fun pt _ => Proof.format pt



mutual

-- tries to prove a sequent with a given rule by trying to prove all the premisses
partial def Proof.byRule (calculus : Calculus) (s : Sequent) (rule : Rule) : Option Proof := do
  -- rule selection and conclusion matching
  let σ     ← Rule.match s rule
  -- subgoal generation
  let ps    ← Rule.substitutePremisses rule σ
  -- proof propagation
  match ps.mapM (prove calculus) with
  | some []    => Proof.Qed s rule
  | some nodes => Proof.Node s rule σ ps nodes
  | none       => none

-- given a sequent and a calculus, get all matching rules and try them until a successful proof is found or they are exhausted
partial def Proof.prove (calculus : Calculus) (s : Sequent) : Option Proof := do
  let seq <- inferTypeIfNeeded s
  match calculus.findSome? (Proof.byRule calculus seq) with
  | some pt => pt
  | none => Proof.Failed s

where
  /- TODO: this is quite ugly, but i don't know how to implement that without this rule. 
   This calculus wouldn't work IMO. It would be great to abstract the prover from the object level calculus
   but this function is highly dependant on the calculus.
   -/
  inferTypeIfNeeded (s : Sequent) : Option Sequent := do
    match s.ty with
      | .Var _ => 
        match Exp.typecheck s.exp with
        | some ty => some {ctx := s.ctx, exp := s.exp, ty := ty}
        | none => some s
      | _ => some s

end


-- Γ, var1:int ⊢ λx:int.var1+x 4:int
#eval Proof.prove simpleTypedLampdaCalculus seq1
-- Γ ⊢ λx:τ.e:τ->τ'
#eval Proof.prove simpleTypedLampdaCalculus seqPr1


#eval intRule.conclusion
#eval seqIntC
#eval seqIntC.exp
#eval intRule.conclusion.exp
#eval Sequent.match intRule.conclusion seqIntC 


end deeep

open deeep

def main : IO Unit := do
  IO.println (Calculus.format simpleTypedLampdaCalculus)
  let pt := (match Proof.prove deeep.simpleTypedLampdaCalculus seq1 with
      |some e => Proof.format e
      |none => "")
  IO.println pt 
