import tactic
import binary
import hamming
import algebra.module.submodule

open B BW

structure binary_linear_code (n m d : ℕ) :=
  (cws : finset (BW n))
  (card_gte : cws.card ≥ 2)
  (is_subspace : subspace B (BW n))

namespace binary_linear_code

instance : Π {n m d : ℕ}, has_mem (BW n) (binary_linear_code n m d) :=
λ n m d, ⟨λ (x : BW n), λ (C : binary_linear_code n m d), x ∈ C.cws⟩

def min_distance {n m d : ℕ} (C : binary_linear_code n m d) : ℕ :=
  finset.min' (finset.image (λ (x : BW n × BW n), d(x.fst, x.snd)) C.cws.off_diag)
  begin
    have : ∃ (x y : BW n), x ∈ C ∧ y ∈ C ∧ x ≠ y, 
    from finset.one_lt_card_iff.mp C.card_gte,
    simp, rw finset.nonempty, simp,
    rcases this with ⟨x, y, ⟨hx, hy, hxy⟩⟩,
    existsi [x, hx, y, hy],
    exact hxy,
  end

notation `d(` C `)` := min_distance C

variables {n m d : ℕ} {C : binary_linear_code n m d}

lemma dist_neq_codewords_gt_min_distance:
  ∀ (c₁ c₂ ∈ C), c₁ ≠ c₂ → d(C) ≤ d(c₁,c₂):=
begin
  intros c₁ c₂ hc₁ hc₂ hneq,
  unfold min_distance,
  apply finset.min'_le,
  simp,
  existsi [c₁, c₂],
  exact ⟨⟨hc₁, hc₂, hneq⟩, rfl⟩,
end

lemma min_distance_pair : ∃ (c₁ c₂ ∈ C), c₁ ≠ c₂ ∧ d(c₁,c₂) = d(C) :=
begin
  have h_mem : d(C) ∈ (finset.image (λ (x : BW n × BW n), d(x.fst, x.snd)) C.cws.off_diag),
  by {rw min_distance, apply finset.min'_mem},
  simp at h_mem,
  rcases h_mem with ⟨x, y, ⟨hx, hy, hneq⟩, h_dist⟩,
  existsi [x, y, hx, hy],
  exact ⟨hneq, h_dist⟩,
end

theorem s_error_detecting_iff_min_distance_gt_s (s : ℕ) : 
  (∀ (x : BW n) (c ∈ C), d(x,c) ≥ 1 ∧ d(x,c) ≤ s → x ∉ C) ↔ d(C) > s :=
begin
  split,
    {contrapose,
    simp,
    intro h_min_dist,
    have : ∃ (c₁ c₂ ∈ C), c₁ ≠ c₂ ∧ d(c₁,c₂) = d(C), from min_distance_pair,
    rcases this with ⟨x, y, hx, hy, ⟨hneq, h_dist_eq_min⟩⟩,
    have h_lte_s : d(x,y) ≤ s, by linarith,
    have h_gte_1 : d(x,y) ≥ 1, from (hamming.distance_neq_between_one_n x y hneq).left,
    existsi [x, y],
    exact ⟨hy, h_gte_1, h_lte_s, hx⟩,
    },
    {intros h x c hc hdist,
    intro hx,
    by_cases heq : x = c,
      {have h_dxc_eq_zero : d(x,c) = 0, from hamming.eq_distance_zero x c heq,
      linarith},
      {have : d(x,c) ≥ d(C), 
      from dist_neq_codewords_gt_min_distance x c hx hc heq,
      linarith,}
    },
end


def change_t_disagreements : Π {n : ℕ}, ℕ → BW n → BW n → BW n
| _ _     nil         nil       := nil
| _ 0     (xhd::ᴮxtl) _         := xhd::ᴮxtl
| _ (t+1) (O::ᴮxtl)   (O::ᴮytl) :=   O::ᴮ(change_t_disagreements t.succ xtl ytl)
| _ (t+1) (I::ᴮxtl)   (I::ᴮytl) :=   I::ᴮ(change_t_disagreements t.succ xtl ytl)
| _ (t+1) (O::ᴮxtl)   (I::ᴮytl) :=   I::ᴮ(change_t_disagreements t      xtl ytl)
| _ (t+1) (I::ᴮxtl)   (O::ᴮytl) :=   O::ᴮ(change_t_disagreements t      xtl ytl)


lemma dist_change_t_disagreements_first_arg {n : ℕ} (t : ℕ) (h₁ : 0 < t) (x y : BW n) (h₂ : t < d(x,y)) : 
  d(x, change_t_disagreements t x y) = t :=
begin
  sorry
end

lemma dist_change_t_disagreements_second_arg {n : ℕ} (t : ℕ) (x y : BW n) :
  d(y, change_t_disagreements t x y) = d(x,y) - t :=
begin
  sorry
end

theorem t_error_correcting_iff_min_distance_gte (t : ℕ) :
  (∀ (c ∈ C) (x : BW n), (d(x,c) ≤ t → (∀ (c' ∈ C), c ≠ c' → d(x,c) < d(x,c'))))
    ↔ d(C) ≥ 2 * t + 1 :=
begin
  split,
    {intro h₁,
    by_contradiction h₂,
    simp at h₂,
    have h₃ : ∃ (c₁ c₂ ∈ C), c₁ ≠ c₂ ∧ d(c₁,c₂) = d(C),
    from min_distance_pair,
    rcases h₃ with ⟨c, c', hc, hc', ⟨hneq, h_dist_eq_min⟩⟩,
    have h₄ : d(c,c') ≤ 2 * t, by linarith,
    have h₅ : d(c, c') ≥ t + 1, 
    by {
      specialize h₁ c hc c',
      by_contradiction h',
      simp at h',
      have h'' : d(c,c') ≤ t, from nat.le_of_lt_succ h',
      rw hamming.distance_symmetric at h'',
      specialize h₁ h'' c' hc' hneq,
      have : d(c',c') = 0, from hamming.eq_distance_zero c' c' rfl,
      rw this at h₁,
      simp at h₁,
      exact h₁,
    },
    have h₆ : ∃ (x : BW n), 1 ≤ d(x,c') ∧ d(x,c') ≤ d(x,c) ∧ d(x,c) = t,
    by {
      use change_t_disagreements t c c',
      have h_d₀ : 1 ≤ d(c,c') ∧ d(c,c') ≤ n, from hamming.distance_neq_between_one_n c c' hneq,
      have h_d₁ : d(c, change_t_disagreements t c c') = t,
      by {apply dist_change_t_disagreements_first_arg; linarith},
      have h_d₂ : d(c', change_t_disagreements t c c') = d(c,c') - t,
      by {apply dist_change_t_disagreements_second_arg},
      rw [hamming.distance_symmetric _ c, hamming.distance_symmetric _ c'],
      split,
        {calc d(c',change_t_disagreements t c c') ≥ d(c,c') - t : by linarith
        ...                                       ≥ t + 1 - t   : by exact nat.sub_le_sub_right h₅ t
        ...                                       = 1           : by simp,},
        split,
        {rw [h_d₁, h_d₂], 
        apply nat.sub_le_left_iff_le_add.mpr,
        conv {congr, skip, ring},
        exact h₄,},
        {linarith}
    },
    rcases h₆ with ⟨x, ⟨h_dxgt1, h_dxc'_le_dxc, h_dxc_eq_t⟩⟩,
    have h_dxc_le_t : d(x,c) ≤ t, by linarith,
    specialize h₁ c hc x h_dxc_le_t c' hc' hneq,
    linarith,
    },
    {intro h,
    intros c hc x h_dist_le_t c' hc' h_c_neq_c',
    have h₁ : d(c,c') ≥ d(C), 
    from dist_neq_codewords_gt_min_distance c c' hc hc' h_c_neq_c',
    have h₂ : d(c,c') ≥ 2 * t + 1, by linarith,
    have h₃ : d(c,c') ≤ d(c,x) + d(x,c'), from hamming.distance_triangle_ineq c c' x,
    calc d(x,c') ≥ d(c,c') - d(c,x)     : by {simp, exact nat.sub_le_left_of_le_add h₃}
    ...          ≥ (2 * t + 1) - d(c,x) : by {simp, exact nat.sub_le_sub_right h₂ d(c,x)}
    ...          ≥ (2 * t + 1) - t      : by {simp, rw hamming.distance_symmetric, 
                                              exact (2 * t + 1).sub_le_sub_left h_dist_le_t}
    ...          = (t + t + 1) - t      : by ring
    ...          = t + 1                : by {rw nat.add_assoc, simp}
    ...          > d(x,c)               : by linarith,
    }
end

end binary_linear_code

def H74C : finset (BW 7) := {
  val := {
    ᴮ[O,O,O,O,O,O,O],
    ᴮ[I,I,O,I,O,O,I],
    ᴮ[O,I,O,I,O,I,O],
    ᴮ[I,O,O,O,O,I,I],
    ᴮ[I,O,O,I,I,O,O],
    ᴮ[O,I,O,O,I,O,I],
    ᴮ[I,I,O,O,I,I,O],
    ᴮ[O,O,O,I,I,I,I],
    ᴮ[I,I,I,O,O,O,O],
    ᴮ[O,O,I,I,O,O,I],
    ᴮ[I,O,I,I,O,I,O],
    ᴮ[O,I,I,O,O,I,I],
    ᴮ[O,I,I,I,I,O,O],
    ᴮ[I,O,I,O,I,O,I],
    ᴮ[O,O,I,O,I,I,O],
    ᴮ[I,I,I,I,I,I,I]
  },
  nodup := by simp,
}

def hamming74Code : binary_linear_code 7 4 3 :=
{
  cws := H74C,
  card_gte := by {have : H74C.card = 16, from rfl, linarith},
  is_subspace := {
    carrier := H74C,
    zero_mem' := by {simp, left, refl},
    add_mem' := begin
      rintros a b
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha)
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb),
        all_goals {
          try {rw list.eq_of_mem_singleton ha}, 
          try {rw list.eq_of_mem_singleton hb}, 
          repeat {{left, refl} <|> right <|> refl},
        },
        all_goals {simp, refl},
    end,
    smul_mem' := begin
      intros c x x_mem,
      cases c,
        {conv {congr, apply_congr zero_smul}, simp, left, refl},
        {conv {congr, apply_congr one_smul}, exact x_mem}
    end,
  },
}

#eval d(hamming74Code)
#eval d(ᴮ[I,I,O,I,O,O,I],ᴮ[O,I,O,I,O,I,O])
def c1 := binary_linear_code.change_t_disagreements 2 ᴮ[I,I,O,I,O,O,I] ᴮ[O,I,O,I,O,I,O]
#eval d(ᴮ[I,I,O,I,O,O,I],c1)
#eval d(ᴮ[O,I,O,I,O,I,O],c1)