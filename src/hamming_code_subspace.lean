import binary
import algebra.module.submodule

open B BW

def code_subspace : subspace B (BW 7) :=
{
  carrier := {
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
  zero_mem' := by {simp, left, refl},
  add_mem' := begin
    rintros a b
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha)
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb),
      all_goals {
        try {rw set.eq_of_mem_singleton ha}, 
        try {rw set.eq_of_mem_singleton hb}, 
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
}