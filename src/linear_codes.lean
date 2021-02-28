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

def exC : finset (BW 5) := {
  val := {
    ᴮ[O,O,O,O,O], 
    ᴮ[I,I,I,I,O], 
    ᴮ[O,I,O,I,I], 
    ᴮ[I,O,I,O,I]
  },
  nodup := by simp,
}


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
  sorry
end

lemma min_distance_lte_range (s : ℕ) (h : min_distance BLC.C BLC.card_gte ≤ s) : ∃ (c₁ c₂ ∈ BLC.C), 1 ≤ d(c₁,c₂) ∧ d(c₁,c₂) ≤ s :=
sorry

lemma s_error_detecting_iff_min_distance_gt_s (s : ℕ) : 
(∀ (x : BW n) (c ∈ BLC.C), d(x,c) ≥ 1 ∧ d(x,c) ≤ s → x ∉ BLC.C) ↔ min_distance BLC.C BLC.card_gte > s :=
begin
  split,
    {contrapose,
    simp,
    intro h_min_dist,
    have : ∃ (c₁ c₂ ∈ BLC.C), 1 ≤ d(c₁,c₂) ∧ d(c₁,c₂) ≤ s, from min_distance_lte_range s h_min_dist,
    rcases this with ⟨c₁, c₂, hc₁, hc₂, ⟨h_gte1, h_ltes⟩⟩,
    existsi [c₁, c₂],
    exact ⟨hc₂, h_gte1, h_ltes, hc₁⟩},
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

end binary_linear_code

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