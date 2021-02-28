import tactic
import binary
import hamming
import algebra.module.submodule

open B BW

def min_distance {n : ℕ} (C : finset (BW n)) (h_card : C.card ≥ 2) : ℕ :=
  finset.min' (finset.image (λ (x : BW n × BW n), d(x.fst, x.snd)) C.off_diag)
  begin
    have : ∃ (x y : BW n), x ∈ C ∧ y ∈ C ∧ x ≠ y, from finset.one_lt_card_iff.mp h_card,
    simp,
    rw finset.nonempty,
    simp,
    rcases this with ⟨x, y, ⟨hx, hy, hxy⟩⟩,
    existsi [x, hx, y, hy],
    exact hxy,
  end


structure binary_linear_code (n m d : ℕ) :=
  (C : finset (BW n))
  (card_gte : C.card ≥ 2)
  (min_distance_is_d : min_distance C card_gte = d)
  (is_subspace : subspace B (BW n))

namespace binary_linear_code

variables {n m d : ℕ} {BLC : binary_linear_code n m d}

lemma dist_neq_codewords_gt_min_distance:
  ∀ (c₁ c₂ ∈ BLC.C), c₁ ≠ c₂ → min_distance BLC.C BLC.card_gte ≤ d(c₁,c₂):=
begin
  intros c₁ c₂ hc₁ hc₂ hneq,
  unfold min_distance,
  apply finset.min'_le,
  simp,
  existsi [c₁, c₂],
  exact ⟨⟨hc₁, hc₂, hneq⟩, rfl⟩,
end

lemma min_distance_pair : ∃ (c₁ c₂ ∈ BLC.C), c₁ ≠ c₂ ∧ d(c₁,c₂) = min_distance BLC.C BLC.card_gte :=
begin
  have h_mem : min_distance BLC.C BLC.card_gte ∈ 
    (finset.image (λ (x : BW n × BW n), d(x.fst, x.snd)) BLC.C.off_diag),
  by {rw min_distance, apply finset.min'_mem},
  simp at h_mem,
  rcases h_mem with ⟨x, y, ⟨hx, hy, hneq⟩, h_dist⟩,
  existsi [x, y, hx, hy],
  exact ⟨hneq, h_dist⟩,
end

theorem s_error_detecting_iff_min_distance_gt_s (s : ℕ) : 
  (∀ (x : BW n) (c ∈ BLC.C), d(x,c) ≥ 1 ∧ d(x,c) ≤ s → x ∉ BLC.C) 
    ↔ min_distance BLC.C BLC.card_gte > s :=
begin
  split,
    {contrapose,
    simp,
    intro h_min_dist,
    have : ∃ (c₁ c₂ ∈ BLC.C), c₁ ≠ c₂ ∧ d(c₁,c₂) = min_distance BLC.C BLC.card_gte, from min_distance_pair,
    rcases this with ⟨x, y, hx, hy, ⟨hneq, h_dist_eq_min⟩⟩,
    have h_lte_s : d(x,y) ≤ s, by linarith,
    have h_gte_1 : d(x,y) ≥ 1, from (hamming.distance_neq_between_zero_n x y hneq).left,
    existsi [x, y],
    exact ⟨hy, h_gte_1, h_lte_s, hx⟩,
    },
    {intros h x c hc hdist,
    intro hx,
    by_cases heq : x = c,
      {have h_dxc_eq_zero : d(x,c) = 0, from hamming.eq_distance_zero x c heq,
      linarith},
      {have : d(x,c) ≥ min_distance BLC.C BLC.card_gte, 
      from dist_neq_codewords_gt_min_distance x c hx hc heq,
      linarith,}
    },
end

theorem t_error_correcting_iff_min_distance_gte (t : ℕ) :
  (∀ (c ∈ BLC.C) (x : BW n), (d(x,c) ≤ t → (∀ (c' ∈ BLC.C), c ≠ c' → d(x,c) < d(x,c'))))
    ↔ min_distance BLC.C BLC.card_gte ≥ 2 * t + 1 :=
begin
  split,
    {sorry},
    {intro h,
    intros c hc x h_dist_lte_t c' hc' h_c_neq_c',
    have h₁ : d(c,c') ≥ min_distance BLC.C BLC.card_gte, 
    from dist_neq_codewords_gt_min_distance c c' hc hc' h_c_neq_c',
    have h₂ : d(c,c') ≥ 2 * t + 1, by linarith,
    have h₃ : d(c,x) ≤ d(c,c') + d(c',x), from hamming.distance_triangle_ineq c x c',
    have h₄ : d(c',x) > d(x,c), 
    calc d(c',x) ≥ d(c,x) - d(c,c')     : by {simp, exact nat.sub_le_left_of_le_add h₃}
    ...          ≥ d(c,x) - (2 * t + 1) : by sorry
    ...          ≥ (2 * t + 1) - t      : by sorry
    ...          = 2 * t + (1 - t)      : by sorry
    ...          = t + 1                : by sorry
    ...          > d(x,c)               : by linarith,
    rw hamming.distance_symmetric at h₄,
    exact h₄,
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
  C := H74C,
  card_gte := by {have : H74C.card = 16, from rfl, linarith},
  min_distance_is_d := rfl,
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

#eval min_distance hamming74Code.C hamming74Code.card_gte