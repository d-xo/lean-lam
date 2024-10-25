import Lean.Parser

-- A deep embedding of the linear lambda calculus

namespace Linear

-- Syntax --

-- qualifiers
inductive q where
| lin
| un

-- booleans
inductive b where
| true
| false

mutual

-- pretypes
inductive P where
| Bool
| Pair : T → T → P
| Arr  : T → T → P

-- types
inductive T where
| T : q → P → T

end

-- terms
inductive t where
| var   : String → t
| bool  : q → b → t
| ite   : t → t → t → t
| pair  : q → t → t → t
| split : t → String → String → t → t
| abs   : q → String → T → t → t
| app   : t → t → t

-- contexts
inductive Γ where
| empty
| comma : Γ → String → T → Γ

-- parser --

declare_syntax_cat qual
syntax "lin" : qual
syntax "un" : qual

declare_syntax_cat boolean
syntax "true" : boolean
syntax "false" : boolean

declare_syntax_cat pretype
declare_syntax_cat type

syntax "Bool" : pretype
syntax type "*" type : pretype
syntax type "→" type : pretype

syntax qual pretype : type

declare_syntax_cat our_term
syntax str : our_term
syntax qual boolean : our_term
syntax "if" our_term "then" our_term "else" our_term : our_term
syntax qual "<" our_term "," our_term ">" : our_term
syntax "split" our_term "as" ident "," ident "in" our_term : our_term
syntax qual "λ" ident ":" type "." our_term : our_term
syntax our_term our_term : our_term

declare_syntax_cat context
syntax "∅" : context
syntax context "," ident ":" type : context

-- Auxiliary notation for translating `lin` into `term`
syntax " ⟪ " our_term " ⟫ " : term
syntax " q⟪ " qual " ⟫ " : term
syntax " t⟪ " type " ⟫ " : term
syntax " p⟪ " pretype " ⟫ " : term
syntax " c⟪ " context " ⟫ " : term

macro_rules
  -- qualifiers
  | `(q⟪ lin ⟫) => `(q.lin)
  | `(q⟪ un ⟫)  => `(q.un)

  -- pretypes
  | `(p⟪ Bool ⟫)  => `(P.Bool)
  | `(p⟪ $l:type * $r:type ⟫)  => `(P.Pair t⟪ $l ⟫ t⟪ $r ⟫ )
  | `(p⟪ $l:type → $r:type ⟫)  => `(P.Arr t⟪ $l ⟫ t⟪ $r ⟫ )

  -- types
  | `(t⟪ $q:qual $p:pretype ⟫)  => `(T.T q⟪ $q ⟫ p⟪ $p ⟫)

  -- terms
  -- TODO: having to use str here is clunky
  | `(⟪ $i:str ⟫)      => `(t.var $i)
  | `(⟪ $q:qual true ⟫)  => `(t.bool q⟪ $q ⟫ b.true)
  | `(⟪ $q:qual false ⟫)  => `(t.bool q⟪ $q ⟫ b.false)
  | `(⟪ if $cond:our_term then $l:our_term else $r:our_term ⟫)  => `(t.ite ⟪ $cond ⟫ ⟪ $l ⟫ ⟪ $r ⟫)
  | `(⟪ $q:qual <$l:our_term, $r:our_term> ⟫)  => `(t.pair q⟪ $q ⟫ ⟪ $l ⟫ ⟪ $r ⟫)
  | `(⟪ split $t:our_term as $x:ident, $y:ident in $subterm:our_term ⟫)  => `(t.split ⟪ $t ⟫ $x $y ⟪ $subterm ⟫)
  | `(⟪ $q:qual λ $i:ident : $ty:type . $body:our_term ⟫) => `(t.abs q⟪ $q ⟫ $i t⟪ $ty ⟫ ⟪ $body ⟫)
  | `(⟪ $x:our_term $y:our_term ⟫) => `(t.app ⟪ $x ⟫ ⟪ $y ⟫)

  -- contexts
  | `(c⟪ ∅ ⟫) => `(Γ.empty)
  | `(c⟪ $ctx:context , $nm:ident : $ty:type ⟫) => `(Γ.comma c⟪ $ctx ⟫ $nm t⟪ $ty ⟫)


#check ⟪ un <"x",lin false> ⟫

-- Formatter --

def COLOR_QUALIFIERS := Bool.false

def qualify (qual : q) (str : String) : String :=
  let color := match qual with
    | .lin => s!"31"
    | .un => s!"34"
  let qual := match qual with
    | .lin => "lin"
    | .un => "un"
  if COLOR_QUALIFIERS
  then s!"\\033[{color}m{str}\\033[0m"
  else s!"{qual} {str}"

def b.format : (val : b) → String
| .true => "true"
| .false => "false"

mutual

def T.format : (ty : T) → String
| .T qual pretype => qualify qual (P.format pretype)

def P.format : (ty : P) → String
| .Bool => "Bool"
| .Pair l r => s!"{T.format l} * {T.format r}"
| .Arr l r => s!"{T.format l} → {T.format r}"

end

def t.format : (term : t) → String
| var s => s
| bool qual val => qualify qual (b.format val)
| ite cond l r => s!"(if {t.format cond} then {t.format l} else {t.format r})"
| pair qual l r => qualify qual (s!"<{t.format l}, {t.format r}>")
| .split term x y subterm => s!"(split {t.format term} as {x},{y} in {t.format subterm})"
| abs qual nm ty body => qualify qual (s!"λ {nm} : {T.format ty} . {t.format body}")
| app l r => s!"{t.format l} {t.format r}"

def Γ.format : (ctx : Γ) → String
| empty => "∅"
| comma head nm ty => s!"{Γ.format head}, {nm} : {T.format ty}"

-- typechecker --

#eval (t.format $ t.bool q.lin b.true)

end Linear
