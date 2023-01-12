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

def not_in_env (γ:env) (x:string) : Prop := (∀ v, (x, v) ∉ γ)

lemma env_sub_lam_notin :
∀ γ x τ e,
  not_in_env γ x →
  env_sub γ (lam x τ e) = lam x τ (env_sub γ e) :=
begin
sorry
end

lemma env_sub_lam_in :
∀ γ x τ e v,
  ((x, v) ∈ γ) →
  env_sub γ (lam x τ e) = lam x τ e :=
begin
sorry
end

-- This is the "substitution lemma" on page 13 of notes.
lemma substitution_lemma :
  ∀ γ x vx e,
  not_in_env γ x →
  env_sub ((x,vx)::γ) e = substitute x vx (env_sub γ e) :=
begin
sorry
end

theorem fundamental_property :
∀ Γ e τ,
  (mk_context Γ ⊢ e : τ) →
  (Γ ⊨ e : τ) :=
begin
  introv Hty,
  generalize h : (mk_context Γ) = (ctx),
  rw h at *,
  induction Hty generalizing Γ; subst h; unfold semantic_has_type,
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
    rename [Hty_x → x, Hty_τ1 → τ1, Hty_τ2 → τ2, Hty_e → e],
    -- FIXME: using this false lemma (could be made true modulo α-substitutions)
    -- to mimic the argument in the lecture notes for now.
    by_cases (not_in_env γ x), tactic.swap,
    { sorry },
    {
      rw env_sub_lam_notin, tactic.swap, { tauto },
      intros e' Hstep,
      cases Hstep with Hstep Hirred,
      cases Hstep, tactic.swap, { cases Hstep_Hstep },
      unfold interp_val,
      split, tactic.swap,
      { unfold closed_vals, constructor },
      constructor,
      intros v Hv,
      -- NOTE: step_closure V⟦τ2⟧ is the same as E⟦τ2⟧.
      rw (_:step_closure V⟦τ2⟧ = E⟦τ2⟧), tactic.swap,
      { unfold interp_exp },

      -- Apply inductive hypothesis
      specialize Hty_ih ((x,τ1)::Γ) _,
      { unfold mk_context },
      specialize Hty_ih ((x,v)::γ) _,
      { constructor, { refl },
        split; assumption,
      },
      unfold env_sub at Hty_ih,
      rw <- substitution_lemma, tactic.swap, assumption,
      apply Hty_ih,
    }
  },
  repeat { sorry }
end
