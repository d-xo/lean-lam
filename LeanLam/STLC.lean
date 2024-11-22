import Aesop
import Mathlib.Tactic

namespace STLC

-- de bruijn levels
  -- raw
  -- fin
  -- dep
-- de bruijn indicies
  -- raw
  -- fin
  -- dep
-- named
  -- raw
  -- dep
-- locally nameless
  -- raw
  -- fin
  -- dep
-- phoas

-- TAPL p103

--- Syntax ---

-- types
inductive T
| Unit : T
| Arr : T → T → T
deriving Repr, BEq, DecidableEq

-- terms (de-bruijn)
inductive t where
| Unit : t
| Var : Nat → t
| Lam : T → t → t
| App : t → t → t
deriving Repr, BEq, DecidableEq

-- context

abbrev Γ := List T

--- Typing ---

inductive types : Γ → t → T → Prop where
| Unit
  : ∀ ctx
  , types ctx .Unit .Unit

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
| .Unit => .Unit
| .Var idx =>
    if idx == depth then (inc new depth 0)
    else if idx > depth then .Var (idx - 1) -- decrement because we stripped a lambda
    else .Var idx
| .Lam ty body => .Lam ty (sub (depth + 1) new body)
| .App f a => .App (sub depth new f) (sub depth new a)
where
  inc (e : t) (amt : Nat) (depth : Nat) : t := match e with
  | .Unit => .Unit
  | .Var i => if i ≥ depth then .Var (i + amt) else .Var i
  | .App f a => .App (inc f amt depth) (inc a amt depth)
  | .Lam ty body => .Lam ty (inc body amt (depth + 1))

-- fully evaluated values
def val : t → Prop
| .Lam _ _ => True
| .Unit => True
| _ => False

inductive eval : t → t → Prop where
| App1
  : ∀ t₁ t'₁ t₂
  , eval t₁ t'₁
  → eval (.App t₁ t₂) (.App t'₁ t₂)

| App2
  : ∀ t₁ t₂ t'₂
  , eval t₂ t'₂
  → val t₁
  → eval (.App t₁ t₂) (.App t₁ t'₂)

| AppAbs
  : ∀ t₁₂ t₂ T₁₁
  , val t₂
  → eval (.App (.Lam T₁₁ t₁₂) t₂) (sub 0 t₂ t₁₂)

--- Proofs ---

def closed : t → Prop := aux 0
where
  aux (depth : Nat) (term : t) : Prop := match term with
  | .Unit => True
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

--- structural properties ---

def t.swap (x y : Nat) : t → t
| .Unit => .Unit
| .App f a => .App (swap x y f) (swap x y a)
| .Lam ty body => .Lam ty (swap (x + 1) (y + 1) body)
| .Var idx =>
  if idx == x then .Var y
  else if idx == y then .Var x
  else .Var idx

def Γ.swap (x y : Nat) (ctx : Γ) : Γ :=
  match ctx[x]?, ctx[y]? with
  | some vx, some vy => ctx |> (List.set · x vy) |> (List.set · y vx)
  | _, _ => ctx

theorem exchange (x y : Nat) (ctx : Γ) (term : t) (ty : T) (hx : x < ctx.length) (hy : y < ctx.length)
  : types ctx term ty → types (ctx.swap x y) (term.swap x y) ty := by
    intro h
    induction term generalizing ty ctx x y with
    | Unit =>
      unfold t.swap
      unfold Γ.swap
      simp_all
      cases h with
      | Unit =>
        exact .Unit ((List.set ctx x ctx[y]).set y ctx[x])
    | App f a ihf iha =>
      cases h with
      | App ctx t₁ t₂ T₁₁ T₁₂  hf ha =>
        exact .App (ctx.swap x y) (f.swap x y) (a.swap x y) T₁₁ ty (ihf x y ctx (.Arr T₁₁ ty) hx hy hf) (iha x y ctx T₁₁ hx hy ha)
    | Var i =>
      unfold t.swap
      split
      case isTrue ht =>
        unfold Γ.swap
        simp_all
        let ctx' := (List.set ctx x ctx[y]).set y ctx[x]
        cases h with
        | Var c i ty' hi => exact .Var ctx' y ty (by aesop)
      case isFalse hf =>
        unfold Γ.swap
        simp_all
        let ctx' := (List.set ctx x ctx[y]).set y ctx[x]
        cases h with
        | Var c i ty' hi =>
          have hvar : t.Var (if i = y then x else i) = if i = y then t.Var x else t.Var i := by aesop
          have skip_ne : ∀ (j a : Nat) (z : Type) (l : List z) (v : z),
            ¬(j = a) → (List.set l a v)[j]? = l[j]? := by
              intros j a z l v hneq
              refine List.getElem?_set_ne ?h
              exact Ne.symm hneq
          have hlookup : ctx'[if i = y then x else i]? = some ty := by aesop
          exact (hvar ▸ .Var ctx' (if i =y then x else i) ty hlookup)
    | Lam ty body ihb =>
      cases h with
      | Abs ctx T₁ T₂ t₂ hb =>
        have : ∀ (k : Nat) (α : Type) (l : List α) (hd : α), k < l.length → k + 1 < (hd :: l).length :=
          by exact fun k α l hd a => Nat.add_lt_of_lt_sub a
        have hswp : (Γ.swap (x + 1) (y + 1) (ty :: ctx)) = (ty :: Γ.swap x y ctx) := by
          unfold Γ.swap; simp_all
        have : types (ty :: Γ.swap x y ctx) (t.swap (x + 1) (y + 1) body) T₂ := by
          exact (hswp ▸ ihb (x + 1) (y + 1) (ty :: ctx) T₂ (by aesop) (by aesop) hb)
        exact .Abs (ctx.swap x y) ty T₂ (body.swap (x + 1) (y + 1)) this

--- Type Soundness ---

-- 9.3.4
theorem cannonical_forms (term : t) (hv : val term) (ht : types ctx term (.Arr T₁ T₂)) : ∃ t₂, term = .Lam T₁ t₂ := by
  unfold val at hv
  cases term with
  | Unit => contradiction
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
  | Unit => left; unfold val; simp
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
      exact ⟨.App t'₁ t₂, .App1 t₁ t'₁ t₂ het1⟩
    | inl vt1 => cases iha' with
      | inr et2 =>
        right
        obtain ⟨t'₂, het2⟩ := et2
        exact ⟨.App t₁ t'₂, .App2 t₁ t₂ t'₂ het2 vt1⟩
      | inl vt2 =>
        obtain ⟨t₁₂, ht12⟩ := cannonical_forms t₁ vt1 hf
        right
        rw [ht12]
        exact ⟨sub 0 t₂ t₁₂, .AppAbs t₁₂ t₂ T₁₁ vt2⟩

theorem types_rfl (htypes : types ctx (t.Lam T₁₁ t₁₂) (.Arr T₁₂ ty)) : T₁₁ = T₁₂ := by
  cases htypes with | Abs => aesop

theorem sub_preserves (ctx : Γ) (S : T) (ty : T) (term : t) (s : t)
  : types (S :: ctx) term ty → types ctx s S → types ctx (sub 0 s term) ty:= by
    intros ht hs
    induction hs with
    | Unit ctx' => sorry
    | Var ctx' n ty' hc =>
      cases ht with
      | Unit =>
        simp_all [sub]
        exact .Unit ctx'
      | App ctx' t₁ t₂ T₁₁ T₁₂ hf ha =>
        exact .App ctx' t₁ t₂ T₁₁ ty sorry sorry
      | Abs => sorry
      | Var ctx' i ty ha =>
        simp_all [sub]
        split
        case isTrue htr =>
          simp_all [sub.inc]
          exact .Var ctx' n ty hc
        case isFalse hfl =>
          have : 0 < i := by omega
          simp [this]
          have : ctx'[i - 1]? = some ty := by
            unfold getElem?
            unfold getElem? at ha
            unfold instGetElem?OfGetElemOfDecidable
            unfold instGetElem?OfGetElemOfDecidable at ha
            simp_all
            obtain ⟨hl, hj⟩ := ha
            have hlen : i - 1 < List.length ctx' := by omega
            have hlen' : ∀ i α (a : α) l, i - 1 < l.length → i < (a :: l).length := by
              intros i α a l hl
              exact lt_of_tsub_lt_tsub_right hl
            have helem (α : Type) (a : α) (l : List α) (hl' : i - 1 < l.length)
              : (a :: l)[i]'(by aesop) = l[i - 1] := by
                  sorry
            have : ctx'[i - 1] = ty := by sorry
            exact ⟨hlen, this⟩
          exact .Var ctx' (i - 1) ty this
    | Abs => sorry
    | App => sorry

theorem preservation (ctx : Γ) (term : t) (term' : t) (ty : T)
  : types ctx term ty → eval term term' → types ctx term' ty := by
    intros htypes heval
    induction heval generalizing ty with
    | App1 t₁ t'₁ t₂ he ih =>
      cases htypes with
      | App ctx t₁ t₂ T₁₁ T₁₂ hf ha =>
        exact .App ctx t'₁ t₂ T₁₁ ty (ih (.Arr T₁₁ ty) hf) ha
    | App2 t₁ t₂ t'₂ he hv ih =>
      cases htypes with
      | App ctx t₁ t₂ T₁₁ T₁₂ hf ha =>
        exact .App ctx t₁ t'₂ T₁₁ ty hf (ih T₁₁ ha)
    | AppAbs t₁₂ t₂ T₁₁ hv =>
      cases htypes with
      | App ctx t₁ t₂ T'₁₁ T₁₂ hf ha =>
        -- TODO; T'₁₁ and T₁₁ should not be distinct vars
        have : T₁₁ = T'₁₁ := by sorry
        simp_all
        cases hf with
        | Abs ctx T₁ T₂ t₂ habs =>
          unfold sub
          sorry

end STLC
