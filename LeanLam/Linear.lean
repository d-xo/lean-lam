-- A deep embedding of the linear lambda calculus

namespace Linear

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

def COLOR_QUALIFIERS := false

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
| true => "true"
| false => "false"

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
| split term x y subterm => s!"(split {t.format term} as {x},{y} in {t.format subterm})"
| abs qual nm ty body => qualify qual (s!"λ {nm} : {T.format ty} . {t.format body}")
| app l r => s!"{t.format l} {t.format r}"

def Γ.format : (ctx : Γ) → String
| empty => "∅"
| comma head nm ty => s!"{Γ.format head}, {nm} : {T.format ty}"

#eval (t.format $ t.bool q.lin b.true)

end Linear
