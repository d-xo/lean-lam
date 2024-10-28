namespace STLC

-- TATP p103

--- Syntax ---

-- types
inductive T
| Arr : T → T → T
deriving Repr, BEq, DecidableEq

-- terms (de-bruijn)
inductive t
| Var : Nat → t
| Lam : T → t → t
| App : t → t → t
deriving Repr, BEq, DecidableEq

-- context

-- TODO: this representation is nice until you need exchange, figure out a better one
abbrev Γ := List T

--- Typing ---

inductive types : Γ → t → T → Prop where
| Var
  : ∀ ctx n ty
  , ctx[n]? = some ty
  → types ctx (.Var n) ty

| Abs
  : ∀ ctx T₁ T₂ t₂
  , types (T₁ :: ctx) t₂ T₂
  → types ctx (.Lam T₁ t₂) (.Arr T₁ T₂)

| App
  : ∀ ctx t₁ t₂ T₁₁ T₁₂
  , types ctx t₁ (.Arr T₁₁ T₁₂)
  → types ctx t₂ T₁₁
  → types ctx (.App t₁ t₂) T₁₂

--- Eval ---

-- substitution
def sub (depth : Nat) (new : t) : t → t
| .Var idx =>
    if idx == depth then (inc new depth 0)
    else if idx > depth then .Var (idx - 1) -- decrement because we stripped a lambda
    else .Var idx
| .Lam ty body => .Lam ty (sub (depth + 1) new body)
| .App f a => .App (sub depth new f) (sub depth new a)
where
  inc (e : t) (amt : Nat) (depth : Nat) : t := match e with
  | .Var i => if i ≥ depth then .Var (i + amt) else .Var i
  | .App f a => .App (inc f amt depth) (inc a amt depth)
  | .Lam ty body => .Lam ty (inc body amt (depth + 1))

-- fully evaluated values
def val : t → Prop
| .Lam _ _ => True
| _ => False

inductive eval : t → t → Prop where
| App1
  : eval t₁ t'₁
  → eval (.App t₁ t₂) (.App t'₁ t₂)

| App2
  : eval t₂ t'₂
  → val t₁
  → eval (.App t₁ t₂) (.App t₁ t'₂)

| AppAbs
  : val t₂
  → eval (.App (.Lam T₁₁ t₁₂) t₂) (sub 0 t₂ t₁₂)

--- Proofs ---

def closed : t → Prop := aux 0
where
  aux (depth : Nat) (term : t) : Prop := match term with
  | .Var n => n < depth
  | .App f a => aux depth f ∧ aux depth a
  | .Lam _ body => aux (depth + 1) body

theorem app_closed_trans (f : t) (a : t) (h : closed (.App f a)) : closed f ∧ closed a := by
  unfold closed at h
  unfold closed.aux at h
  unfold closed
  assumption

-- 9.3.1
namespace inversions

theorem var (h : types ctx (.Var n) R) : ctx[n]? = some R := by
  cases h
  assumption

theorem abs (h : types ctx (.Lam T₁ t₂) R) : ∃ R₂, R = .Arr T₁ R₂ ∧ types (T₁ :: ctx) t₂ R₂ := by
  cases h with | Abs c T₁ T₂ t₂ pre  => exact ⟨ T₂ , by simp; assumption ⟩

theorem app (h : types ctx (.App t₁ t₂) R) : ∃ T₁₁, types ctx t₁ (.Arr T₁₁ R) ∧ types ctx t₂ T₁₁ := by
  cases h with | App ctx t₁ t₂ T₁₁ T₁₂  hf ha => exact ⟨T₁₁, ⟨hf, ha⟩⟩

end inversions

-- 9.3.4
theorem cannonical_forms (term : t) (hv : val term) (ht : types ctx term (.Arr T₁ T₂)) : ∃ t₂, term = .Lam T₁ t₂ := by
  unfold val at hv
  cases term with
  | Var n => contradiction
  | App f a => contradiction
  | Lam Tₐ body =>
    simp at hv
    obtain ⟨R₂, ⟨harr, _⟩⟩ := inversions.abs ht
    have : Tₐ = T₁ := by
      injection harr with h _
      exact h.symm
    rw [this]
    exact ⟨body, rfl⟩

theorem progress (term : t) (ty : T) : closed term → ctx = [] → types ctx term ty → val term ∨ ∃ term', eval term term' := by
  intros hclosed hempty htypes
  induction htypes with
  | Var ih n => contradiction
  | Abs ctx' T₁ _ t₂ => left; simp [val]
  | App ctx' t₁ t₂ T₁₁ T₁₂ hf _ ihf iha =>
    have hfcl : closed t₁ := And.left (app_closed_trans t₁ t₂ hclosed)
    have hacl : closed t₂ := And.right (app_closed_trans t₁ t₂ hclosed)
    have ihf' : val t₁ ∨ ∃ term', eval t₁ term' := ihf hfcl hempty
    have iha' : val t₂ ∨ ∃ term', eval t₂ term' := iha hacl hempty
    cases ihf' with
    | inr et1 =>
      right
      obtain ⟨t'₁, het1⟩ := et1
      exact ⟨.App t'₁ t₂, .App1 het1⟩
    | inl vt1 => cases iha' with
      | inr et2 =>
        right
        obtain ⟨t'₂, het2⟩ := et2
        exact ⟨.App t₁ t'₂, .App2 het2 vt1⟩
      | inl vt2 =>
        obtain ⟨t₁₂, ht12⟩ := cannonical_forms t₁ vt1 hf
        right
        rw [ht12]
        exact ⟨sub 0 t₂ t₁₂, .AppAbs vt2⟩

theorem preservation (ctx : Γ) (term : t) (term' : t) (ty : T) : types ctx term ty ∧ eval term term' → types ctx term' ty := by sorry

end STLC
