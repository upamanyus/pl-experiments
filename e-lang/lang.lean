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

open exp
open typ

-- Statics:
def context := (string → option typ)
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
| t_cat: ∀ (e1 e2:exp) Γ, has_type Γ e1 str → has_type Γ e2 str → has_type Γ (cat e1 e2) str
| t_len: ∀ (e1:exp) Γ, has_type Γ e1 str → has_type Γ (len e1) num
| t_let: ∀ x (e1 e2:exp) Γ τ1 τ2 (He1 : has_type Γ e1 τ1) (He2:has_type (x ↦ τ1 ; Γ) e2 τ2),
                        has_type Γ (elet x e1 e2) τ2

def substitute (x':string) (e':exp) : exp → exp
| (var y) := if (x' = y) then e' else var y
| (lit_num n) := lit_num n
| (lit_str s) := lit_str s
| (plus e1 e2) := plus (substitute e1) (substitute e2)
| (times e1 e2) := times (substitute e1) (substitute e2)
| (cat e1 e2) := cat (substitute e1) (substitute e2)
| (len e1) := len (substitute e1)
| (elet y e1 e2) := if (x' = y) then elet y e1 e2 else elet y (substitute e1) (substitute e2)

-- Dynamics
inductive is_val : exp → Prop
| v_num : ∀ n, is_val (lit_num n)
| v_str : ∀ s, is_val (lit_str s)

inductive is_step : exp → exp → Prop
| s_plus : ∀ (n1 n2 n:ℕ), n = n1 + n2 → is_step (plus (lit_num n1) (lit_num n2)) (lit_num n)
| s_cat : ∀ (s1 s2 s:string), s = s1 ++ s2 → is_step (cat (lit_str s1) (lit_str s2)) (lit_str s)
| s_len : ∀ s, is_step (len (lit_str s)) (lit_num (string.length s))
| s_let : ∀ x e1 e2, is_step (elet x e1 e2) (substitute x e1 e2) -- NOTE: this is call by-value
-- the rest of these are the "search" transitions
| s_plus_l : ∀ e1 e2 e1', is_step e1 e1' → is_step (plus e1 e2) (plus e1' e2)
| s_plus_r : ∀ e1 e2 e2', is_step e2 e2' → is_step (plus e1 e2) (plus e1 e2')
| s_cat_l : ∀ e1 e2 e1', is_step e1 e1' → is_step (cat e1 e2) (cat e1' e2)
| s_cat_r : ∀ e1 e2 e2', is_step e2 e2' → is_step (cat e1 e2) (cat e1 e2')

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

-- XXX: we aren't modding out by α-equivalence, so the statement is slightly
-- stronger so that the inductive hypothesis is stronger; without this,
-- weakening for `let` doesn't work.
theorem weakening' :
∀ (Γ Γ':context) e' τ',
context_included Γ Γ' →
has_type Γ e' τ' →
has_type Γ' e' τ'
:=
begin
  introv,
  intros Hinc Hty,
  revert Γ',
  induction Hty,
  case has_type.t_let : x e1 e2 Γ _ _ He1 He2 Hih1 Hih2 {
    intros Γ' Hinc,
    specialize Hih1 _ Hinc,
    specialize Hih2 (x ↦ Hty_τ1 ; Γ') _,
    {
      apply included_update,
      assumption,
    },
    apply has_type.t_let,
    assumption,
    assumption,
  },
  {
    intros Γ' Hinc,
    apply has_type.t_var,
    apply Hinc,
    assumption,
  },
  {
    intros Γ' Hinc,
    apply has_type.t_lit_str,
  },
  {
    intros Γ' Hinc,
    apply has_type.t_lit_num,
  },
  {
    intros Γ' Hinc,
    apply has_type.t_plus,
    { apply Hty_ih_ᾰ, assumption },
    { apply Hty_ih_ᾰ_1, assumption },
  },
  {
    intros Γ' Hinc,
    apply has_type.t_times,
    { apply Hty_ih_ᾰ, assumption },
    { apply Hty_ih_ᾰ_1, assumption },
  },
  {
    intros Γ' Hinc,
    apply has_type.t_cat,
    { apply Hty_ih_ᾰ, assumption },
    { apply Hty_ih_ᾰ_1, assumption },
  },
  {
    intros Γ' Hinc,
    apply has_type.t_len,
    { apply Hty_ih, assumption },
  },
end

/--
theorem weakening_bad :
∀ (Γ:context) e' τ' x τ,
Γ x = none →
has_type Γ e' τ' →
has_type (x ↦ τ ; Γ) e' τ'
:=
begin
  introv,
  intros Hfresh Hty,
  revert x,
  induction Hty,
  -- pretty_cases,
  case has_type.t_let : x e1 e2 Γ _ _ He1 He2 Hih1 Hih2 {
    dedup,
    intros xnew Hfresh,
    specialize Hih1 _ Hfresh,
    specialize Hih2 xnew,
    { suffices : x ≠ x,
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
-/
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
