import Mathlib.Tactic

--- Types ---

inductive Ty where
  | unit : Ty
  | fn   : Ty → Ty → Ty

notation "()" => Ty.unit
infixl:30 " → " => Ty.fn

--- Typing Contexts ---

inductive Ctx where
  | nil : Ctx
  | snoc : Ctx → Ty → Ctx

infixl:100 (priority := 0) " ; " => Ctx.snoc

@[reducible,simp] def Ctx.length : Ctx → ℕ
  | .nil => 0
  | .snoc Γ _ => .succ (Ctx.length Γ)

/-- Returns the `Ty` at the provided index in `Γ`. -/
@[reducible] def Ctx.get : (Γ : Ctx) → Fin Γ.length → Ty
  | (_ ; α), ⟨0, _⟩ => α
  | (Γ ; _), ⟨.succ x, p⟩ => Γ.get ⟨x, by aesop⟩

instance : EmptyCollection Ctx where
  emptyCollection := .nil

instance : GetElem Ctx Nat Ty (λ Γ i => i < Γ.length) where
  getElem Γ i p := Γ.get ⟨i, p⟩

--- Membership Judgment ---

inductive Mem : Ty → Ctx → Type
  | h : Mem α (Γ ; α)
  | t : Mem α Γ → Mem α (Γ ; β)

-- can't use built in `Membership` class since that requires a `Prop`, and we
-- need `Mem` to be a type  has to be a `Type` to be able to implement `extend'`
infixl:60 (priority := high) " ∈ " => Mem

--- Typing Judgment ---

inductive Types : Ctx → Ty → Type
  | unit : Types Γ ()
  | var  : {Γ : Ctx} → {α : Ty} → α ∈ Γ → Types Γ α
  | lam  : Types (Γ ; arg) ret → Types Γ (arg → ret)
  | app  : Types Γ (arg → ret) → Types Γ arg → Types Γ ret

notation "()"  => Types.unit
notation "λ ."  => Types.lam
infix:67 " ● " => Types.app
prefix:67 "↖" => Types.var
infix:67 " ⊢ " => Types

--- DB Index Abbreviations ---

/-- Returns a proof of membership for the type at `n` in `Γ`. -/
@[reducible,simp] def count : {Γ : Ctx} → (n : Fin Γ.length) → Γ[n] ∈ Γ
  | (_ ; _), ⟨0, _⟩ => .h
  | (_ ; _), ⟨.succ x, p⟩ => .t (count ⟨x, by aesop⟩)

/-- Ensures that the context is correctly captured and passed down to the child terms. -/
@[reducible,simp] def var! {Γ : Ctx} {α : Ty} (n : Fin Γ.length) (p : Γ[n] = α) : Types Γ α :=
  p ▸ Types.var (count n)

set_option quotPrecheck false
notation "#" n:arg => (var! n (by apply Eq.refl))
set_option quotPrecheck true

--- Renaming ---

/-- Takes a map (`ρ`) from variables in `Γ` to variables in `Δ` and produces a new
    mapping from `Γ` extended with `β` to `Δ` extended with `β` -/
def extend (ρ : ∀ {α}, α ∈ Γ → α ∈ Δ) : α ∈ Γ ; β → α ∈ Δ ; β
  | .h => .h
  | .t m => .t (ρ m)

/-- Takes a map (`ρ`) from variables in `Γ` to variables in `Δ`, and applies
    that map to each variable in a term under `Γ` to produce a new semantically
    identical term under `Δ` -/
def rename (ρ : ∀ {α}, α ∈ Γ → α ∈ Δ) : Γ ⊢ β → Δ ⊢ β
  | ↖i => .var (ρ i)
  | () => .unit
  | fn ● arg => .app (rename ρ fn) (rename ρ arg)
  | λ . body => .lam (rename (extend ρ) body)

--- Substitution ---

def extend' (σ : ∀ {α}, α ∈ Γ → Δ ⊢ α) : α ∈ Γ ; β → Δ ; β ⊢ α
  | .h => .var .h
  | .t x => rename .t (σ x)

def substitute (σ : ∀ {α}, α ∈ Γ → Δ ⊢ α) : Γ ⊢ α → Δ ⊢ α
  | ↖i => σ i
  | () => .unit
  | fn ● arg => .app (substitute σ fn) (substitute σ arg)
  | λ . body => .lam (substitute (extend' σ) body)

def sub1 (a : Γ ; β ⊢ α) (b : Γ ⊢ β) : Γ ⊢ α := substitute σ a
  where
    σ {γ : Ty} : (m : γ ∈ Γ ; β) → (Γ ⊢ γ)
      | .h => b
      | .t m => .var m

notation a:arg "[" b:arg "]" => sub1 a b

--- Values ---

inductive Val : Γ ⊢ α → Prop
  | unit : Val ()
  | lam  : {body : Γ ; α ⊢ β} → Val (λ . body)

--- Reduction ---

inductive Reduce : Γ ⊢ α → Γ ⊢ α → Type
  | ξ₁ : Reduce fn fn' → Reduce (fn ● arg) (fn' ● arg)
  | ξ₂ : Val fn → Reduce arg arg' → Reduce (fn ● arg) (fn ● arg')
  | β  : Reduce ((λ . body) ● arg) (body [ arg ])

--- Type Soundness ---

/-!
We get preservation for "free" via the definition of `Reduce` and `substitute`
which encode it directly into their type signatures
-/

inductive Progress : Γ ⊢ α → Prop
  | step : Reduce a b → Progress a
  | done : Val a → Progress a

/-- Every closed term is either a value or can be reduced -/
theorem progress : (t : ∅  ⊢ α) → Progress t
  | () => .done .unit
  | λ . body => .done .lam
  | fn ● arg => match progress fn with
    | .step rf => .step (.ξ₁ rf)
    | .done vf => match progress arg with
      | .step ra => .step (.ξ₂ vf ra)
      | .done _ => by cases fn with (try contradiction)
        | lam body => exact .step .β

--- Evaluation ---

inductive Eval : Γ ⊢ α → Γ ⊢ α → Type
  | refl : Eval a a
  | step : Eval b c → Reduce a b → Eval a c

def Gas := ℕ

inductive Done : Γ ⊢ α → Type
  | done : Val t → Done t
  | oog  : Done t

inductive Steps : ∅ ⊢ α → Prop
  | steps : Eval a b → Done b → Steps a

-- TODO: rm gas
def eval : Gas → (t : ∅ ⊢ α) → Steps t
  | .zero, _ => .steps .refl .oog
  | .succ g, t => match progress t with
    | (@Progress.step _ _ _ b r) => match eval g b with
      | .steps evl fin => .steps (.step evl r) fin
    | .done v => .steps .refl (.done v)

--- Booleans ---

def x : Γ ⊢ (() → (() → ())) := λ . (λ . (#1))
