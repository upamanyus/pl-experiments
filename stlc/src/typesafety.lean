import lang
import data.set

-- V⟦−⟧ : type → PowerSet(ClosedVal)
-- V⟦−⟧ : type → (ClosedVal → 2)
-- interp_val : type → val → Prop
--

open exp typ

notation e ` ↦* `:90 e' := is_many_step e e'

def irred (e:exp) := ¬(∃ e', e ↦str e')

-- Approach to defining inductive relation inspired from ModuRes.

def T := set exp
instance T_has_mem : has_mem (exp) T := set.has_mem
instance T_has_inter : has_inter T := set.has_inter

def step_closure (s:T) : T :=
  { e:exp | ∀ e', (e ↦* e') ∧ irred(e') → e' ∈ s }

inductive rel_arrow: T → T → T
| Rlam (Rτ1 Rτ2:T) (x:string) (τ:typ) (e:exp)
  (Hfunc: ∀ (v:exp), (v ∈ Rτ1) → (substitute x v e) ∈ step_closure Rτ2) :
  (rel_arrow Rτ1 Rτ2 (lam x τ e))

def closed_vals := { e : exp | is_val e }

def interp_val : typ → (set exp)
| unitT := (singleton exp.unit)
| (arrowT τ1 τ2) := (rel_arrow (interp_val τ1) (interp_val τ2)) ∩ closed_vals

def interp_exp (τ:typ) := step_closure (interp_val τ)

notation `V⟦` τ `⟧` := interp_val τ
notation `E⟦` τ `⟧` := interp_exp τ

-- XXX: now, we're gonna call context_list Γ, and have to explicitly to
-- (mk_context Γ) in has_type.
def interp_ctx : context_list → set env
| [] [] := true
| ((y,τ)::Γ) ((x,v)::γ) := x=y ∧ interp_ctx Γ γ ∧ (v ∈ V⟦τ⟧)
| _ _ := false

notation `G⟦` Γ `⟧` := interp_ctx Γ

def semantic_has_type (Γ:context_list) (e:exp) (τ:typ) : Prop :=
  ∀ γ, γ ∈ G⟦Γ⟧ → env_sub γ e ∈ E⟦τ⟧

notation Γ ` ⊨ `:90 e:90 ` : `:90 τ := semantic_has_type Γ e τ

def safe (e:exp) : Prop :=
∀ e', (e ↦* e') → (is_val e') ∨ (∃ e'', e' ↦str e'')

lemma interp_val_implies_closedval :
∀ v τ, v ∈ V⟦τ⟧ → v ∈ closed_vals :=
begin
  introv Hval,
  cases τ,
  {
      unfold interp_val at Hval,
      unfold singleton at Hval,
      simp at Hval, subst Hval,
      constructor
  },
  {
      unfold interp_val at Hval,
      cases Hval,
      unfold closed_vals at Hval_right,
      simp at Hval_right, assumption
  }
end

lemma semantic_implies_type_safety :
∀ e τ,
  ([] ⊨ e : τ) →
  safe(e) :=
begin
  introv HTy,
  intros e' Hstep,
  by_cases irred(e'), tactic.swap,
  { -- easy case, just take a step
    unfold irred at h,
    simp at h,
    cases h with e'',
    right,
    existsi e'',
    assumption
  },
  { -- otherwise, show
    unfold semantic_has_type at HTy,
    specialize HTy [] _,
    { constructor },
    unfold env_sub at HTy,
    specialize HTy e' ⟨Hstep, h⟩,
    left,
    apply interp_val_implies_closedval,
    assumption
  }
end

theorem fundamental_property :
∀ Γ e τ,
  (mk_context Γ ⊢ e : τ) →
  (Γ ⊨ e : τ) :=
begin
  introv Hty,
  unfold semantic_has_type,
  generalize h : (mk_context Γ) = (ctx),
  rw h at *,
  induction Hty generalizing Γ; subst h,
  { -- case: unit
    introv Hγ, rw env_sub_unit,
    unfold interp_exp step_closure, simp *,
    introv Hstep Hirred,
    cases Hstep,
    { constructor },
    exfalso, cases Hstep_Hstep,
  },
  { -- case: var
    introv Hγ,
    rename [Hty_x → x, Hty_τ → τ],
    -- Argument:
    -- Knowing (mk_context Γ) x = some τ and γ ∈ G⟦Γ⟧ should tells us:
    -- ∃ (x,vx) ∈ γ, vx ∈ V⟦τ⟧,
    --    env_sub γ (var x) = vx
    -- At that point, we're done because V⟦τ⟧ ⊆ E⟦τ⟧.
    sorry,
  },
  { -- case: abs; this is where induction will be a bit tricky.
    introv Hγ,
    sorry,
  },
  repeat { sorry }
end
