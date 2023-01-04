-- import tactic

inductive typ : Type
| num : typ
| str : typ

inductive exp : Type
| var : string → exp
| lit_num : ℕ → exp
| lit_str : string → exp
| plus : exp → exp → exp
| times : exp → exp → exp
| cat : exp → exp → exp
| len : exp → exp
| elet : string → exp → exp → exp

def context := (string → option typ)
open exp
open typ

def update_context (Γ:context) (x:string) (t:typ) : context :=
  λ y,
  if x = y then
  some t
  else Γ y

notation x `↦` τ `;` Γ := update_context Γ x τ

inductive has_type : context → exp → typ → Prop
| t_var : ∀ (Γ:context) x t, (Γ x = some t) → has_type Γ (var x) t
| t_lit_str: ∀ (s:string) Γ, has_type Γ (lit_str s) str
| t_lit_num: ∀ (n:ℕ) Γ, has_type Γ (lit_num n) num
| t_plus: ∀ (e1 e2:exp) Γ,  has_type Γ e1 num → has_type Γ e2 num →
                        has_type Γ (plus e1 e2) num
| t_times: ∀ (e1 e2:exp) Γ, has_type Γ e1 num → has_type Γ e2 num →
                        has_type Γ (times e1 e2) num
| t_cat: ∀ (e1 e2:exp) Γ, has_type Γ e1 str → has_type Γ (cat e1 e2) str
| t_len: ∀ (e1:exp) Γ, has_type Γ e1 str → has_type Γ (len e1) num
| t_let: ∀ x (e1 e2:exp) Γ τ1 τ2 (He1 : has_type Γ e1 τ1) (He2:has_type (x ↦ τ1 ; Γ) e2 τ2),
                        has_type Γ (elet x e1 e2) τ2

-- FIXME: The let rule is messed up. Need to assume that x ∉ Γ.

-- FIXME: notation needs to be surrounded by parens to work correctly

theorem typing_unicity :
∀ Γ e τa τb,
has_type Γ e τa →
has_type Γ e τb →
(τa = τb) :=
begin
intros Γ _ _ _ H1 H2,
revert τb,
induction H1,
case has_type.t_let : x e1 e2 Γ _ _ He1 He2 Hih1 Hih2 {
  dedup,
  intros τb H2,
  cases H2,
  specialize Hih1 H2_τ1 H2_He1,
  subst Hih1,
  specialize Hih2 _ H2_He2,
  assumption,
},
{
  intros τb H2,
  cases H2,
  rw H2_ᾰ at H1_ᾰ,
  injection H1_ᾰ,
  rw h_1,
},
{
  intros τb H2,
  cases H2,
  refl,
},
{
  intros τb H2,
  cases H2,
  refl,
},
{
  intros τb H2,
  cases H2,
  refl,
},
{
  intros τb H2,
  cases H2,
  refl,
},
{
  intros τb H2,
  cases H2,
  refl,
},
{
  intros τb H2,
  cases H2,
  refl,
}
end

theorem weakening :
∀ (Γ:context) e' τ' x τ,
Γ x = none →
has_type Γ e' τ' →
has_type (x ↦ τ ; Γ) e' τ'
:=
begin
  introv,
  intros Hfresh Hty,
  induction Hty,
  -- pretty_cases,
  case has_type.t_let : x e1 e2 Γ _ _ He1 He2 Hih1 Hih2 {
    dedup,
    specialize Hih1 Hfresh,
    specialize Hih2 _,
    { suffices : x_1 ≠ x,
      { unfold update_context,
        rwa if_neg,
        assumption,
      },
      sorry -- FIXME: want fresh name for x_1
    },
    apply has_type.t_let,
    assumption,
    suffices h : ((x_1 ↦ Hty_τ1 ; (x↦τ;Γ_1)) = (x↦τ;(x_1 ↦ Hty_τ1 ; Γ_1))),
    { rwa h },
    unfold update_context,
    apply funext,
    intros y,
    by_cases (x_1 = y),
    {
      by_cases (x = y),
      { sorry }, -- FIXME: want x_1 ≠ x
      { simp * },
    },
    {
      by_cases (x = y),
      { simp * },
      { simp * },
    }
  },
  {
    apply has_type.t_var,
    unfold update_context,
    by_cases (x = Hty_x),
    {
      subst h,
      exfalso,
      rw Hfresh at Hty_ᾰ,
      contradiction,
   },
   rw if_neg,
   { assumption },
   { assumption },
  },
  { apply has_type.t_lit_str },
  { apply has_type.t_lit_num },
  {
    apply has_type.t_plus,
    { apply Hty_ih_ᾰ, assumption },
    { apply Hty_ih_ᾰ_1, assumption },
  },
  {
    apply has_type.t_times,
    { apply Hty_ih_ᾰ, assumption },
    { apply Hty_ih_ᾰ_1, assumption },
  },
  {
    apply has_type.t_cat,
    { apply Hty_ih, assumption },
  },
  {
    apply has_type.t_len,
    { apply Hty_ih, assumption },
  },
end

--  intros H1
--  revert τb
--  induction H1 with
--  | t_var => intro τb H2 ; cases H2; simp_all
--  | t_lit_str => intro τb H2 ; cases H2; simp_all
--  | t_lit_num => intro τb H2 ; cases H2; simp_all
--  | t_plus => intro τb H2 ; cases H2; simp_all
--  | t_times => intro τb H2 ; cases H2; simp_all
--  | t_cat => intro τb H2 ; cases H2; simp_all
--  | t_len => intro τb H2 ; cases H2; simp_all
--  | t_let _ _ H4 H5 =>
--  -- this is broken; not sure how to get the inductive hypothesis with names...
--    intro τb H2
--    cases H2 with
--    | t_let _ _ Hn Hm =>
--    simp_all
