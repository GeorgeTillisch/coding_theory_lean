import tactic
import binary
import hamming
import binary_codes
import algebra.module.submodule

/-!
# Linear Binary Codes

This file contains the definition of a linear binary code.
We also use this definition to formalize the Hamming(7,4) code 
and some of its properties.
-/

open B BW binary_code

structure linear_binary_code (n M d : ℕ) extends binary_code n M d :=
  (is_subspace : subspace B (BW n))

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

def hamming74Code : linear_binary_code 7 16 3 :=
{
  cws := H74C,
  has_card_M := rfl,
  card_gte := by {have : H74C.card = 16, from rfl, linarith},
  has_min_distance_d := rfl,
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

lemma hamming74Code_2_error_detecting : 
  hamming74Code.to_binary_code.error_detecting 2 := 
begin
  rw [s_error_detecting_iff_min_distance_gt_s, hamming74Code.has_min_distance_d],
  linarith,
end

lemma hamming74Code_1_error_correcting :
  hamming74Code.to_binary_code.error_correcting 1 :=
begin
  rw [t_error_correcting_iff_min_distance_gte, hamming74Code.has_min_distance_d],
  linarith,
end

lemma hamming74Code_perfect :
  hamming74Code.to_binary_code.perfect :=
begin
  unfold perfect,
  rw [hamming74Code.has_card_M],
  simp,
  refl,
end