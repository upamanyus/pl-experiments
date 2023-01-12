import tactic.basic

inductive typ : Type
| unitT : typ
| arrowT (τ1:typ) (τ2:typ) : typ

inductive exp : Type
| var (x:string) : exp
| unit : exp
| lam (x:string) (τ:typ) (e:exp) : exp
| ap (f:exp) (a:exp) : exp

open exp
open typ

-- FIXME: should move partial functions to separate file
-- Statics:
def context := string → option typ

def update_context (Γ:context) (x:string) (t:typ) : context :=
  λ y, if (x = y) then t else Γ y

notation x `↦` τ `;` Γ := update_context Γ x τ
def empty_ctx : context := (λ _, none)

-- def context_lookup : context → string → option typ
-- | [] x := none
-- | ((y, τ) :: l) x := if x = y then τ else context_lookup l x

inductive has_type : context → exp → typ → Prop
| unit (Γ:context) : has_type Γ unit unitT
| var (Γ:context) (x:string) (τ:typ) (Hvar:Γ x = some τ) : has_type Γ (var x) τ
| lam (Γ:context) (x:string) (τ1 τ2:typ) (e:exp) (Habs:has_type (x↦τ1 ; Γ) e τ2) : has_type Γ (lam x τ1 e) (arrowT τ1 τ2)
| ap  (Γ:context) (f a:exp) (τ1 τ2:typ) (Hfunc:has_type Γ f (arrowT τ1 τ2)) (Hargs:has_type Γ a τ1): has_type Γ (ap f a) τ2

def substitute (x':string) (e':exp) : exp → exp
| unit := unit
| (var x) := if (x' = x) then e' else (var x)
| (lam x τ e) := if (x' = x) then (lam x τ e) else (lam x τ (substitute e))
| (ap f a) := (ap (substitute f) (substitute a))

-- Dynamics
inductive is_val : exp → Prop
| v_unit : is_val unit
| v_lam : ∀ x τ e, is_val (lam x τ e)

-- structural dynamics
inductive is_step : exp → exp → Prop
| ap (x:string) (τ:typ) (e a:exp): is_step (ap (lam x τ e) a) (substitute x a e)
| ap_f (e e' a:exp) (Hstep:is_step e e') : is_step (ap e a) (ap e' a)
-- NOTE: this is call by name. Chosen because it has fewer rules.
--
notation e ` ↦str `:90 e' := is_step e e'

notation Γ ` ⊢ `:90 e:90 ` : `:90 τ:90 := has_type Γ e τ

inductive is_many_step : exp → exp → Prop
| many_steps_reflexive e:exp : is_many_step e e
| many_steps_transitive (e1 e2 e3:exp) (Hsteps:is_many_step e2 e3) (Hstep:is_step e1 e2)
   : is_many_step e1 e3

-- Plan is to prove:
-- a) (∅ ⊢ e:τ) implies SN τ e;
-- b) SN τ e → normalizes e.
-- Proving b is easy by induction, it's basically baked into the definition
-- Proving a by induction on (∅ ⊢ e:τ) will be tricky in the has_type.lam case.

-- def env := finmap (λ _:string, exp)
def env := list (string × exp)
-- def env := alist (λ _:string, exp)

def env_sub : env → exp → exp
| [] e := e
| (⟨x, ex⟩::l) e := env_sub l (substitute x ex e)

instance env_has_mem : has_mem (string × exp) env := list.has_mem

def context_list := list (string × typ)
def mk_context : context_list → context
| [] := empty_ctx
| ((x,τ) :: ctx) := (x↦τ; mk_context ctx)

def is_env_ctx (P:typ → exp → Prop) : env → context_list → Prop
| [] [] := true
| ((x,v)::γ) ((y,τ)::Γ) := x=y ∧ is_env_ctx γ Γ ∧ P τ v
| _ _ := false

-- FIXME: copy/paste from e-lang
def context_included (Γ Γ':context) : Prop :=
  ∀ x y,
    Γ x = some y → Γ' x = some y

def included_update :
∀ Γ Γ' x τ,
 context_included Γ Γ' →
 context_included (x ↦ τ ; Γ) (x ↦ τ ; Γ')
 :=
begin
 introv,
 intros Hinc,
 unfold context_included update_context at *,
 intros x1 y Hlookup,
 by_cases (x = x1),
 { rwa if_pos at *; assumption,
 },
 rw if_neg at * ; try { assumption },
 { apply Hinc, assumption }
end

def empty_included:
  ∀ Γ, context_included empty_ctx Γ :=
begin
  intros,
  intros _ _ H,
  exfalso, unfold empty_ctx at *, contradiction
end

lemma weakening :
  ∀ Γ' Γ e τ,
  context_included Γ' Γ →
  Γ' ⊢ e : τ →
  Γ ⊢ e : τ :=
begin
  introv Hinc Hty,
  induction Hty generalizing Γ,
  { /- case: unit -/ constructor },
  { /- case: var -/ constructor, apply Hinc, assumption },
  { -- case: lam
    constructor,
    apply Hty_ih,
    apply included_update,
    assumption,
  },
  { -- case: ap
    constructor,
    { apply Hty_ih_Hfunc, assumption },
    { apply Hty_ih_Hargs, assumption },
  }
end

lemma sub_property :
∀ x τx v Γ e τ,
empty_ctx ⊢ v : τx →
(x ↦ τx; Γ) ⊢ e : τ →
Γ ⊢ substitute x v e : τ :=
begin
  introv Hty Hty,
  generalize h : (x↦τx;Γ) = Γ',
  rw h at *,
  induction Hty generalizing Γ; subst h,
  { unfold substitute, constructor },
  { unfold substitute,
    unfold update_context at Hty_Hvar,
    by_cases (x = Hty_x),
    {
      simp *,
      simp * at Hty_Hvar,
      injection Hty_Hvar,
      subst h_1,
      apply weakening,
      tactic.swap, assumption,
      apply empty_included
    },
    {
      rw if_neg at *;
      try { tauto },
      constructor,
      assumption
    }
  },
  { -- case: lam
    unfold substitute,
    by_cases (x = Hty_x),
    {
      simp *,
      constructor,
      subst h,
      have h : (x↦Hty_τ1;(x↦τx;Γ)) = (x↦Hty_τ1;Γ),
      { unfold update_context, apply funext, intros y,
        by_cases (x = y),
        { simp * },
        { repeat { rw (if_neg h)} }
      },
      rw <- h,
      assumption
    },
    {
      rw if_neg, tactic.swap, trivial,
      constructor,
      apply Hty_ih,
      unfold update_context,
      apply funext,
      intros y,
      by_cases (x = y),
      { subst h, simp *, rw if_neg, tauto },
      { rw if_neg, tactic.swap, tauto, by_cases (Hty_x = y),
        { simp * },
        { repeat { rw if_neg }, repeat { assumption }},
      },
    },
  },
  { -- case : ap
    unfold substitute,
    constructor,
    { apply Hty_ih_Hfunc, refl },
    { apply Hty_ih_Hargs, refl }
  }
end

lemma substitution_property :
  ∀ γ Γ c e τ P,
  is_env_ctx P γ c →
  (∀ v' τ', (P τ' v') → (empty_ctx ⊢ v' : τ')) →
  Γ = mk_context c →
  Γ ⊢ e : τ →
  empty_ctx ⊢ env_sub γ e : τ
  :=
begin
  introv Henv Hclosed HΓ Hty,
  subst HΓ,
  induction γ generalizing c e,
  {
    induction c,
    { unfold env_sub, unfold empty_ctx, assumption },
    { exfalso, unfold is_env_ctx at Henv, trivial },
  },
  induction c,
  { exfalso, cases γ_hd, unfold is_env_ctx at Henv, trivial },
  cases γ_hd with x v,
  unfold env_sub,
  cases c_hd,
  unfold is_env_ctx at Henv,
  apply (γ_ih c_tl),
  { apply Henv.2.1 },
  cases Henv with Hre Henv,
  subst Hre,
  apply sub_property,
  tactic.swap,
  { exact Hty, },
  { cases c_hd_snd; cases Henv with _ Hsn; apply Hclosed; apply Hsn },
end

lemma env_sub_unit :
∀ γ, env_sub γ unit = unit :=
begin
 intros,
 induction γ,
 { unfold env_sub, },
 { cases γ_hd, unfold env_sub, unfold substitute, assumption },
end

lemma env_sub_ap :
∀ γ f a, (env_sub γ (ap f a)) = (ap (env_sub γ f) (env_sub γ a)) :=
begin
  intros,
  induction γ generalizing f a,
  { unfold env_sub, },
  cases γ_hd,
  unfold env_sub,
  apply γ_ih,
end

lemma env_sub_lam_val :
∀ γ x τ e, is_val (env_sub γ (lam x τ e)) :=
begin
  intros,
  induction γ generalizing e,
  { unfold env_sub, constructor },
  cases γ_hd, unfold env_sub,
  unfold substitute,
  by_cases (γ_hd_fst = x),
  { simp * },
  rw if_neg, tactic.swap, trivial,
  apply γ_ih,
end

lemma sub_lam_ne :
∀ (Γ:context) y ey τ2 e,
(∀ x τx, Γ x = some τx → y ≠ x) →
Γ ⊢ e : τ2 →
(substitute y ey e) = e :=
begin
  introv Hne Hty,
  induction Hty,
  { unfold substitute },
  { unfold substitute, rw if_neg,
    apply Hne,
    { assumption },
  },
  {
    unfold substitute,
    by_cases (y = Hty_x),
    { simp * },
    { rw if_neg, tactic.swap, trivial,
      rw Hty_ih,
      { introv Hlookup,
        unfold update_context at Hlookup,
        by_cases (Hty_x = x),
        { simp * at Hlookup, subst h, tauto },
        { rw if_neg at Hlookup, apply Hne, assumption, assumption },
      }
    }
  },
  {
    unfold substitute,
    rw Hty_ih_Hfunc,
    rw Hty_ih_Hargs,
    repeat { assumption }
  },
end

lemma env_sub_closed :
∀ γ v τ, (empty_ctx ⊢ v : τ) → env_sub γ v = v :=
begin
  introv Hsn,
  generalize h : empty_ctx = Γ,
  rw h at *,
  induction Hsn generalizing γ; subst h,
  { apply env_sub_unit },
  { exfalso, unfold empty_ctx at Hsn_Hvar, contradiction },
  {
    induction γ,
    { unfold env_sub },
    cases γ_hd,
    unfold env_sub,
    unfold substitute,
    by_cases (γ_hd_fst = Hsn_x),
    { simp * },
    { rw if_neg, tactic.swap, trivial,
      rw sub_lam_ne,
      { apply γ_ih },
      tactic.swap, assumption,
      { intros, unfold update_context at *, by_cases Hsn_x = x,
        { simp *, subst h, tauto },
        { rw if_neg at *, unfold empty_ctx at *, contradiction, assumption }
      }
    }
  },
  { rw env_sub_ap,
    rw Hsn_ih_Hfunc,
    rw Hsn_ih_Hargs,
    repeat { trivial },
  },
end

lemma double_substitute :
∀ x τ1 τ2 ex1 ex2 e,
empty_ctx ⊢ ex1 : τ1 →
empty_ctx ⊢ ex2 : τ2 →
(substitute x ex2 (substitute x ex1 e)) = substitute x ex1 e :=
begin
intros,
  induction e,
  { unfold substitute, by_cases (x = e),
    { simp *,
      have h : (substitute e ex2 ex1 = env_sub [(e,ex2)] ex1),
      { unfold env_sub },
      rw h,
      rw env_sub_closed,
      assumption
    },
    {
      rw if_neg, tactic.swap, trivial,
      unfold substitute, rw if_neg, trivial
    }
  },
  { unfold substitute },
  {
    unfold substitute,
    by_cases (x = e_x),
    { simp *, unfold substitute, simp * },
    { rw if_neg, tactic.swap, trivial,
      unfold substitute, rw if_neg, tactic.swap, trivial,
      rw e_ih,
    }
  },
  {
    unfold substitute,
    rw [e_ih_f, e_ih_a]
  }
end

lemma substitute_commute :
∀ x y τx τy ex ey e,
(empty_ctx ⊢ ex : τx) →
(empty_ctx ⊢ ey : τy) →
x ≠ y →
(substitute x ex (substitute y ey e)) = (substitute y ey (substitute x ex e)) :=
begin
  intros,
  induction e,
  { -- case: var
    unfold substitute,
    by_cases (y = e),
    { simp *, subst h,
      rw if_neg, tactic.swap, trivial,
      unfold substitute,
      simp *,
      have h : (substitute x ex ey = env_sub [(x,ex)] ey),
      { unfold env_sub },
      rw h, apply env_sub_closed, assumption
    },
    {
      rw if_neg, tactic.swap, trivial,
      unfold substitute,
      by_cases (x = e),
      {
        simp *,
        have h : (substitute y ey ex = env_sub [(y,ey)] ex),
        { unfold env_sub },
        rw h, rw env_sub_closed, assumption
      },
      {
        rw if_neg, unfold substitute, rw if_neg, repeat { assumption }
      }
    }
  },
  { -- case: unit
    unfold substitute,
  },
  { -- case: lam
    unfold substitute,
    by_cases (y = e_x); by_cases (x = e_x),
    { simp *, unfold substitute, simp * },
    { simp *, unfold substitute, rw if_neg, simp *, assumption },
    { rw if_neg, simp *, unfold substitute, simp *, assumption },
    { rw if_neg, rw if_neg, unfold substitute, simp *, assumption, assumption },
  },
  { -- case: ap
    unfold substitute,
    rw e_ih_f,
    rw e_ih_a,
  }
end

