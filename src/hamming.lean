import tactic
import binary

namespace hamming

open B BW

def distance : Π {n : ℕ}, BW n → BW n → ℕ
| _ nil       nil       := nat.zero
| _ (O ::ᴮ x) (O ::ᴮ y) := distance x y
| _ (I ::ᴮ x) (I ::ᴮ y) := distance x y
| _ (_ ::ᴮ x) (_ ::ᴮ y) := nat.succ (distance x y)

notation `d(` x `,` y `)` := distance x y

variables {n : ℕ}

@[simp]
lemma distance_self_zero (x : BW n) : d(x,x) = 0 :=
begin
  induction x with _ hd _ ih,
    refl,
  cases hd; {rw distance, exact ih}
end

lemma distance_eq_zero_same_head (hd₁ hd₂ : B) (tl₁ tl₂ : BW n) (h : distance (hd₁ ::ᴮ tl₁) (hd₂ ::ᴮ tl₂) = 0) : hd₁ = hd₂ :=
by cases hd₁; cases hd₂; {refl <|> contradiction}

@[simp]
lemma distance_hd_eq_same_distance_tail (hd₁ hd₂ : B) (tl₁ tl₂ : BW n) (h : hd₁ = hd₂) : distance (hd₁ ::ᴮ tl₁) (hd₂ ::ᴮ tl₂) = distance tl₁ tl₂ :=
by cases hd₁; cases hd₂; {refl <|> contradiction}

lemma distance_zero_eq (x y : BW n) : d(x,y) = 0 → (x = y) :=
λ h : d(x,y) = 0,
begin
  induction x with _ xhd xtl ih,
    {apply eq.symm, apply nil_unique},
  cases y with _ yhd ytl,
  have hds_eq : xhd = yhd, apply distance_eq_zero_same_head xhd yhd xtl ytl h,
  rw distance_hd_eq_same_distance_tail at h,
    {have tls_eq : xtl = ytl, from ih ytl h,
    rw hds_eq, rw tls_eq},
    {exact hds_eq}
end

lemma eq_distance_zero (x y : BW n) : (x = y) → d(x,y) = 0 :=
λ h : x = y, by {rw h, simp}

@[simp]
theorem distance_zero_iff_eq (x y : BW n) : d(x,y) = 0 ↔ (x = y) :=
iff.intro 
  (distance_zero_eq x y)
  (eq_distance_zero x y)

@[simp]
lemma distance_succ_one_eq (x y : BW n) : d(x,y).succ = 1 ↔ x = y :=
begin
  split,
    {intro h,
    rw ← nat.add_one at h, 
    norm_num at h,
    exact h},
    {intro h,
    have h_d_zero : d(x,y) = 0, from eq_distance_zero x y h,
    rw h_d_zero,}
end

@[simp]
lemma distance_hd_neq_same_succ_distance_tail (hd₁ hd₂ : B) (tl₁ tl₂ : BW n) (h : hd₁ ≠ hd₂) : distance (hd₁ ::ᴮ tl₁) (hd₂ ::ᴮ tl₂) = nat.succ d(tl₁,tl₂) :=
by cases hd₁; cases hd₂; {refl <|> contradiction}

theorem distance_symmetric : ∀ (x y : BW n), d(x,y) = d(y,x) :=
begin
  intros,
  induction x with _ xhd xtl ih,
    {rw nil_unique y},
    {cases y with _ yhd ytl, cases xhd; cases yhd; {simp, apply ih}},
end

lemma distance_between_zero_n : ∀ (x y : BW n), 0 ≤ d(x,y) ∧ d(x,y) ≤ n :=
begin 
  intros,
  split,
    {simp},
    {induction x with m xhd xtl ih,
      {cases y, refl},
      {cases y with _ yhd ytl,
        cases xhd;
          {cases yhd;
            {simp, 
            have : d(xtl,ytl) ≤ m, from ih ytl,
            apply nat.le_succ_of_le,
            exact this}
            <|>
            {rw distance_hd_neq_same_succ_distance_tail, 
              {have : d(xtl,ytl) ≤ m, from ih ytl, 
              rwa nat.succ_le_succ_iff},
              {contradiction}
            }
          }
      }
    }
end

lemma distance_neq_between_one_n : ∀ (x y : BW n), x ≠ y → 1 ≤ d(x,y) ∧ d(x,y) ≤ n :=
begin
  intros x y hneq,
  have h₁ : 0 ≤ d(x,y) ∧ d(x,y) ≤ n, from distance_between_zero_n x y,
  have h₂ : d(x,y) ≠ 0, from λ (heq : d(x,y) = 0), absurd (distance_zero_eq x y heq) hneq,
  split,
    {apply nat.pos_of_ne_zero h₂},
    {exact h₁.right}
end

theorem distance_triangle_ineq : ∀ (x y z : BW n), d(x,y) ≤ d(x,z) + d(z,y) :=
begin
intros,
induction n with m ih,
  {rw [nil_unique x, nil_unique y, nil_unique z],
  refl},
  {
    cases x with _ xhd xtl,
    cases y with _ yhd ytl,
    cases z with _ zhd ztl, 
    have ih_instance : d(xtl,ytl) ≤ d(xtl,ztl) + d(ztl,ytl), by apply ih,
    by_cases h₁ : xhd = yhd,
      {
        rw distance_hd_eq_same_distance_tail,
        rw h₁,
        rw distance_symmetric (yhd::ᴮxtl)(zhd::ᴮztl),
        cases zhd,
          show xhd = yhd, by exact h₁,
          repeat {
            {cases yhd;
              {simp, 
              rw distance_symmetric ztl xtl,
              exact h}
              <|>
              {simp,
              rw distance_symmetric ztl xtl,
              repeat {rw nat.succ_eq_add_one}, 
              linarith, 
              }
            }
          },
      },
      {
        rw distance_hd_neq_same_succ_distance_tail,
        show xhd ≠ yhd, by exact h₁,
        cases xhd;
          {cases yhd;
            {contradiction}
            <|>
            {cases zhd;
              {simp,
              repeat {rw nat.succ_eq_add_one},
              linarith}
            }
          }
      }
  }
end

def weight : Π {n : ℕ}, BW n → ℕ
| _ nil       := nat.zero
| _ (O ::ᴮ x) := weight x
| _ (I ::ᴮ x) := nat.succ (weight x)

notation `wt(` x `)` := weight x

lemma weight_eq_distance_zero : ∀ (x : BW n), wt(x) = d(x, (BW.zero n)) :=
begin
  intro x,
  induction x with _ xhd xtl ih,
    {refl},
  cases xhd; {rw [zero, weight], simp, exact ih}
end

lemma distance_eq_weight_of_sum : ∀ (x y : BW n), d(x,y) = wt((x + y)) :=
begin
  intros x y,
  induction n with m ih,
    {rw [nil_unique x, nil_unique y], refl},
  cases x with _ xhd xtl,
  cases y with _ yhd ytl,
  cases xhd; cases yhd; 
  {simp,
  conv {to_rhs, congr, apply_congr add_hds},
  conv {to_rhs, congr, congr, whnf},
  rw weight,
  try {simp}, 
  apply ih
  }
end

end hamming