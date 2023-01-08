import data.list.basic
import data.finmap

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

-- FIXME: should partial functions to separate file
-- Statics:
def context := list (string × typ)

def update_context (Γ:context) (x:string) (t:typ) : context :=
  (x, t) :: Γ
notation x `↦` τ `;` Γ := update_context Γ x τ
def empty_ctx : context := []

def context_lookup : context → string → option typ
| [] x := none
| ((y, τ) :: l) x := if x = y then τ else context_lookup l x

inductive has_type : context → exp → typ → Prop
| unit (Γ:context) : has_type Γ unit unitT
| var (Γ:context) (x:string) (τ:typ) (Hvar:context_lookup Γ x = some τ) : has_type Γ (var x) τ
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
| many_steps_transitive (e1 e2 e3:exp) (Hsteps:is_many_step e1 e2) (Hstep:is_step e2 e3)
   : is_many_step e1 e3

def evals_to (e v:exp) : Prop := is_many_step e v ∧ is_val v
def normalizes (e:exp) : Prop := ∃ v, evals_to e v

-- Proof of strong normalization using a logical predicate
def SN : typ → exp → Prop
| unitT e := (empty_ctx ⊢ e : unitT) ∧ (normalizes e)
| (arrowT τ1 τ2) e := (empty_ctx ⊢ e : arrowT τ1 τ2) ∧
                      (normalizes e) ∧
                      (∀ (e':exp), (SN τ1 e') → (SN τ2 (ap e e')))

-- Plan is to prove:
-- a) (∅ ⊢ e:τ) implies SN τ e;
-- b) SN τ e → normalizes e.
-- Proving b is easy by induction, it's basically baked into the definition
-- Proving a by induction on (∅ ⊢ e:τ) will be tricky in the has_type.lam case.

lemma bad_SN_a :
  ∀ e τ,
  empty_ctx ⊢ e:τ →
  SN τ e :=
begin
  introv Hty,
  generalize h:empty_ctx = Γ,
  rw h at *,
  induction Hty; subst h,
  { -- case: unit
    sorry,
  },
  { -- case: var
    exfalso, sorry
  },
  { -- case: lam abstraction
    unfold SN,
    split,
    { constructor; assumption },
    split,
    { sorry },
    intros a Hsna,
    rename [Hty_x → x, Hty_e → e, Hty_τ1 → τ1, Hty_τ2 → τ2, Hty_Habs → Habs],
    sorry,
  },
  sorry,
end

-- def env := finmap (λ _:string, exp)
def env := list (string × exp)

def env_sub : env → exp → exp
| [] e := e
| ((x, ex) :: l) e := env_sub l (substitute x ex e)

instance env_has_mem : has_mem (string × exp) env := list.has_mem

-- noncomputable def env_sub : env → exp → exp
-- | γ e :=
--   match (γ.entries.to_list) with
--   | [] := e
--   | ((sigma.mk x ex) :: l) := (substitute x ex e)
--   end

def is_env_ctx : env → context → Prop
| [] [] := true
| ((x,v)::γ) ((y,τ)::Γ) := x=y ∧ is_env_ctx γ Γ ∧ SN τ v
| _ _ := false

lemma sub_property :
∀ x τx v Γ e τ,
empty_ctx ⊢ v : τx →
(x ↦ τx; Γ) ⊢ e : τ →
Γ ⊢ substitute x v e : τ :=
begin sorry end

lemma substitution_property :
  ∀ γ Γ e τ ,
  is_env_ctx γ Γ →
  Γ ⊢ e : τ →
  empty_ctx ⊢ env_sub γ e : τ
  :=
begin
  introv Henv Hty,
  induction γ generalizing Γ e,
  {
    induction Γ,
    { unfold env_sub, unfold empty_ctx, assumption },
    { exfalso, unfold is_env_ctx at Henv, trivial },
  },
  induction Γ,
  { exfalso, cases γ_hd, unfold is_env_ctx at Henv, trivial },
  cases γ_hd with x v,
  unfold env_sub,
  cases Γ_hd,
  unfold is_env_ctx at Henv,
  apply (γ_ih Γ_tl),
  { apply Henv.2.1 },
  cases Henv with Hre Henv,
  subst Hre,
  apply sub_property,
  tactic.swap,
  { exact Hty, },
  { cases Γ_hd_snd; cases Henv with _ Hsn; apply Hsn.1 },
end

lemma sn_preservation :
  ∀ e e' τ,
  empty_ctx ⊢ e : τ →
  (e ↦str e') →
  (SN τ e' → SN τ e) ∧
  (SN τ e → SN τ e') :=
begin sorry end

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

-- FIXME: this lemma is false. If γ has an instantiation for x in it, then this
-- is wrong.
lemma env_sub_lam :
∀ γ x τ e, (env_sub γ (lam x τ e)) = lam x τ (env_sub γ e) :=
begin sorry end

lemma env_sub_sn :
∀ γ v τ, SN τ v → env_sub γ v = v :=
begin
  introv Hsn,
  have h : (empty_ctx ⊢ v : τ),
  {
    cases τ; exact Hsn.1
  },
  clear Hsn,
  generalize h : empty_ctx = Γ,
  rw h at *,
  induction h generalizing γ; subst h,
  { apply env_sub_unit },
  { exfalso, unfold empty_ctx context_lookup at h_Hvar, contradiction },
  { rw env_sub_lam, sorry }, -- FIXME: the lemma env_sub_lam is false, and makes this unprovable
  { rw env_sub_ap,
    rw h_ih_Hfunc,
    rw h_ih_Hargs,
    repeat { trivial },
  },
end

lemma sn_implies_normalizes :
∀ e τ, SN τ e → normalizes e :=
begin
 introv Hsn,
 cases τ, exact Hsn.2, exact Hsn.2.1
end

theorem sn_general :
  ∀ Γ γ e τ,
  Γ ⊢ e : τ →
  is_env_ctx γ Γ →
  SN τ (env_sub γ e) :=
begin
  introv Hty Henv,
  induction Hty generalizing γ,
  { -- case: unit
    rw env_sub_unit,
    unfold SN,
    split,
    { constructor },
    existsi exp.unit,
    unfold evals_to,
    split; constructor
  },
  { -- case: var
    induction γ generalizing Hty_Γ,
    {
      induction Hty_Γ,
      { exfalso, unfold context_lookup at *, contradiction },
      { exfalso, unfold is_env_ctx at *, contradiction }
    },
    induction Hty_Γ,
    { exfalso, unfold context_lookup at *, contradiction },
    cases γ_hd, cases Hty_Γ_hd,
    unfold is_env_ctx at *,
    unfold env_sub,
    cases Henv with Hre Henv,
    subst Hre,
    by_cases (Hty_x = γ_hd_fst),
    { -- the first thing in Γ/γ is the var Hty_x
      subst h,
      unfold env_sub substitute at Hty_Γ_ih,
      unfold context_lookup at Hty_Hvar,
      unfold substitute at *,
      simp * at *,
      injection Hty_Hvar,
      subst h_1,
      rw (env_sub_sn _ _ _ Henv.2),
      apply Henv.2
    },
    { -- induction
      unfold substitute, rw if_neg,
      tactic.swap, { tauto, },
      apply γ_ih,
      {
        unfold context_lookup at Hty_Hvar,
        rw if_neg at Hty_Hvar,
        tactic.swap, { assumption },
        assumption,
      },
      { apply Henv.1, },
    },
  },
  { -- case: lam. This is the tricky case
    rename [Hty_x → x, Hty_τ1→τ1, Hty_τ2→τ2, Hty_e→e, Hty_Γ → Γ],
    unfold SN,
    split,
    { -- property 1 in notes
      apply substitution_property,
      { assumption },
      constructor, assumption
    },
    split,
    { -- property 2 in notes
      existsi _,
      unfold evals_to,
      split,
      apply is_many_step.many_steps_reflexive,
      rw env_sub_lam,
      constructor,
    },
    -- property 3
    intros e' Hsn,
    have h := (sn_implies_normalizes _ _ Hsn),
    cases h with w Heval,
    cases Heval with Hsteps Hval,

    apply (sn_preservation _ _ τ2 _ _).1,
    tactic.rotate 2,
    {
      constructor,
      { apply substitution_property,
        assumption, constructor, assumption
      },
      cases τ1; apply Hsn.1, -- this could be a separate lemma
    },
    {
      rw env_sub_lam,
      -- FIXME: this is where the proof goes wrong and the env_sub and
      -- substitute end up in the wrong order. The lemma env_sub_lam is false.
      constructor,
    },
    -- XXX: here, our proof diverges from the notes because we are doing
    -- call-by-name but the notes are doing call-by-value

    have h: (env_sub ((x,e')::γ) e) = (substitute x e' (env_sub γ e)),
    {
      unfold env_sub,

      sorry, -- FIXME: the notes say this, but not clear if/why it's true. Maybe env_sub is defined incorrectly?
    },
    rw <- h,
    apply Hty_ih,
    unfold update_context,
    unfold is_env_ctx,
    split, refl,
    split, assumption,
    assumption,
  },
  { -- case: ap
    specialize Hty_ih_Hfunc _ Henv,
    specialize Hty_ih_Hargs _ Henv,
    unfold SN at Hty_ih_Hfunc,
    rw env_sub_ap,
    apply Hty_ih_Hfunc.2.2,
    apply Hty_ih_Hargs
  }
end
