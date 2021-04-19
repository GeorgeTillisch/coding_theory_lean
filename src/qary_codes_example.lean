import tactic

namespace qary_hamming
-- Setup for defining vectors over a finite alphabet 𝒜
universe u
variables {𝒜 : Type u} [fintype 𝒜] [decidable_eq 𝒜] [field_𝒜: field 𝒜]

def distance : Π {n : ℕ}, vector 𝒜 n → vector 𝒜 n → ℕ
| 0       _ _ := 0
| (n + 1) x y :=
  if x.head = y.head then
    distance x.tail y.tail
  else
    nat.succ (distance x.tail y.tail)

variable (n : ℕ)

@[simp]
lemma distance_self_zero (x : vector 𝒜 n) : distance x x = 0 :=
begin
  induction n with k ih,
    refl,
  unfold distance, simp, apply ih, 
end

lemma distance_zero_eq (x y : vector 𝒜 n) : distance x y = 0 ↔ (x = y) :=
begin
  split,
    {intro h,
    induction n with k ih,
      simp,
    unfold distance at h,
    by_cases h' : x.head = y.head,
      {rw h' at h, simp at h,
      have : x.tail = y.tail, from ih _ _ h,
      rw [(vector.cons_head_tail x).symm, (vector.cons_head_tail y).symm, h', this]},
      {by_contradiction hneq,
      simp only [if_congr, h', if_false] at h, 
      rw ← nat.add_one at h, simp at h,
      exact h,}},
  intro h, rw h, simp,
end

def weight : Π {n : ℕ}, vector 𝒜 n → ℕ 
| 0 _ := 0
| (n + 1) x :=
  if x.head = field_𝒜.zero then
    weight x.tail
  else
    nat.succ (weight x.tail)

end qary_hamming

-- Some examples, using an alphabet of size 4
@[derive [decidable_eq, fintype]]
inductive D : Type
| a : D
| b : D
| c : D
| d : D

open D

#eval qary_hamming.distance ⟨[a,a,a,a], rfl⟩ ⟨[a,b,b,a], rfl⟩ -- 2
#eval qary_hamming.distance ⟨[a,b,c,d], rfl⟩ ⟨[d,c,b,a], rfl⟩ -- 4
