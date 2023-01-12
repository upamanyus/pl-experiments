import lang

open typ exp

def evals_to (e v:exp) : Prop := is_many_step e v ∧ is_val v
def normalizes (e:exp) : Prop := ∃ v, evals_to e v

-- Proof of strong normalization using a logical predicate
def SN : typ → exp → Prop
| unitT e := (empty_ctx ⊢ e : unitT) ∧ (normalizes e)
| (arrowT τ1 τ2) e := (empty_ctx ⊢ e : arrowT τ1 τ2) ∧
                      (normalizes e) ∧
                      (∀ (e':exp), (SN τ1 e') → (SN τ2 (ap e e')))

lemma sn_implies_closed :
∀ e τ,
 SN τ e → empty_ctx ⊢ e : τ :=
begin
  intros,
  cases τ; unfold SN at *; tauto
end

lemma sn_implies_normalizes :
∀ e τ, SN τ e → normalizes e :=
begin
 introv Hsn,
 cases τ, exact Hsn.2, exact Hsn.2.1
end

lemma sn_preservation :
  ∀ e e' τ,
  empty_ctx ⊢ e : τ →
  (e ↦str e') →
  (SN τ e' → SN τ e) -- ∧ (SN τ e → SN τ e')
:=
begin
introv Hty Hstep,
{ -- backwards preservation
  intros Hsn,
  generalize h : (empty_ctx = Γ),
  rw h at *,
  -- induction Hty generalizing e'; subst h,
  induction τ generalizing e' e; subst h,
  -- cases Hstep,
  -- induction Hty; subst h,
  {
    unfold SN,
    split, assumption,
    have h := (sn_implies_normalizes _ _ Hsn),
    cases h,
    existsi h_w,
    unfold evals_to at *,
    split,
    { apply is_many_step.many_steps_transitive,
      apply h_h.1, assumption
    },
    apply h_h.2,
  },
  { unfold SN,
    split,
    { assumption },
    split,
    {
      have h := (sn_implies_normalizes _ _ Hsn),
      cases h,
      existsi h_w,
      unfold evals_to at *,
      cases h_h,
      split,
      {
        apply is_many_step.many_steps_transitive,
        { assumption },
        assumption
      },
      assumption
    },
    cases Hstep,
    {
      unfold SN at Hsn,
      intros a Hsna,
      apply τ_ih_τ2,
      { constructor, assumption  },
      { apply Hsn.2.2, assumption },
      constructor,
      { assumption },
      cases τ_τ1; apply Hsna.1,
    },
    {
      intros a Hsna,
      unfold SN at Hsn,
      apply τ_ih_τ2,
      { constructor, assumption },
      { apply Hsn.2.2, assumption },
      constructor,
      { assumption },
      cases τ_τ1; apply Hsna.1,
    }
  },
},
end

-- XXX: this is a tricky lemma because of variable shadowing. If we worked
-- modulo α-equivalence, this trickiness might be avoided.
lemma env_sub_lam_step :
∀ γ c x τ1 e e',
is_env_ctx SN γ c →
SN τ1 e' →
(env_sub γ (lam x τ1 e)).ap e' ↦str (env_sub γ (substitute x e' e)) :=
begin
  introv Hctx Hsn,
  induction γ generalizing e c,
  { unfold env_sub, constructor },
  cases γ_hd with y vy,
  unfold env_sub,
  unfold substitute,
  by_cases (y = x),
  {
    simp *,
    cases c,
    { exfalso, unfold is_env_ctx at *, assumption },
    cases c_hd,
    unfold is_env_ctx at Hctx,
    rw double_substitute,
    { apply γ_ih, apply Hctx.2.1 },
    { apply sn_implies_closed, assumption },
    { apply sn_implies_closed, apply Hctx.2.2 },
  },
  {
    rw if_neg, tactic.swap, tauto,
    cases c,
    { exfalso, unfold is_env_ctx at *, assumption },
    cases c_hd,
    unfold is_env_ctx at Hctx,
    rw substitute_commute,
    {
      apply γ_ih,
      { apply Hctx.2.1 },
    },
    { apply sn_implies_closed, apply Hctx.2.2 },
    { apply sn_implies_closed, assumption },
    { assumption },
  }
end

theorem sn_general :
  ∀ Γ c γ e τ,
  Γ = mk_context c →
  Γ ⊢ e : τ →
  is_env_ctx SN γ c →
  SN τ (env_sub γ e) :=
begin
  introv HΓ Hty Henv,
  induction Hty generalizing γ c; subst HΓ,
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
    induction γ generalizing c,
    {
      induction c,
      { exfalso, contradiction },
      { exfalso, unfold is_env_ctx at *, contradiction }
    },
    induction c,
    { exfalso, contradiction },
    cases γ_hd, cases c_hd,
    unfold is_env_ctx at *,
    unfold env_sub,
    cases Henv with Hre Henv,
    subst Hre,
    by_cases (Hty_x = γ_hd_fst),
    { -- the first thing in Γ/γ is the var Hty_x
      subst h,
      unfold env_sub substitute at c_ih,
      unfold substitute at *,
      simp * at *,
      unfold mk_context update_context at Hty_Hvar,
      simp * at Hty_Hvar,
      injection Hty_Hvar,
      subst h_1,
      rw (env_sub_closed _ _ _ _),
      { apply Henv.2 },
      tactic.swap, { apply sn_implies_closed, apply Henv.2 },
    },
    { -- induction
      unfold substitute, rw if_neg,
      tactic.swap, { tauto, },
      unfold mk_context update_context at Hty_Hvar,
      rw if_neg at Hty_Hvar,
      tactic.swap, { tauto },
      apply γ_ih,
      { apply Henv.1, },
      { assumption }
    },
  },
  { -- case: lam. This is the tricky case
    rename [Hty_x → x, Hty_τ1→τ1, Hty_τ2→τ2, Hty_e→e],
    unfold SN,
    split,
    { -- property 1 in notes
      apply substitution_property,
      { assumption },
      { intros, apply sn_implies_closed, assumption },
      { refl },
      constructor, assumption
    },
    split,
    { -- property 2 in notes
      existsi _,
      unfold evals_to,
      split,
      apply is_many_step.many_steps_reflexive,
      apply env_sub_lam_val,
    },
    -- property 3
    intros e' Hsn,
    have h := (sn_implies_normalizes _ _ Hsn),
    cases h with w Heval,
    cases Heval with Hsteps Hval,

    apply (sn_preservation _ _ τ2 _ _),
    tactic.rotate 2,
    {
      constructor,
      { apply substitution_property,
        assumption, apply sn_implies_closed,
        refl, constructor, assumption
      },
      cases τ1; apply Hsn.1, -- this could be a separate lemma
    },
    {
      apply env_sub_lam_step,
      { assumption },
      { assumption }
    },
    -- XXX: here, our proof diverges from the notes because we are doing
    -- call-by-name but the notes are doing call-by-value

    have h: (env_sub ((x,e')::γ) e) = (env_sub γ (substitute x e' e)),
    { unfold env_sub },
    rw <- h,
    apply Hty_ih _ ((x, τ1) :: c),
    { unfold mk_context },
    unfold is_env_ctx,
    split, refl,
    split, assumption,
    assumption,
  },
  { -- case: ap
    specialize Hty_ih_Hfunc _ _ _ Henv, trivial,
    specialize Hty_ih_Hargs _ _ _ Henv, trivial,
    unfold SN at Hty_ih_Hfunc,
    rw env_sub_ap,
    apply Hty_ih_Hfunc.2.2,
    apply Hty_ih_Hargs
  }
end

theorem strong_normalization :
  ∀ e τ, (empty_ctx ⊢ e : τ) → normalizes e :=
begin
  introv Hty,
  have h := (sn_general empty_ctx [] [] e τ _ Hty _),
  { apply sn_implies_normalizes, assumption },
  { unfold mk_context },
  { unfold is_env_ctx },
end
