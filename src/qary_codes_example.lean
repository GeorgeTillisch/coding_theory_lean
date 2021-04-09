import tactic

-- Setup for defining the hamming distance 
-- between two vectors over a finite alphabet 𝒜
universe u
variables {𝒜 : Type u} [fintype 𝒜] [decidable_eq 𝒜]

def hamming_distance : Π {n : ℕ}, vector 𝒜 n → vector 𝒜 n → ℕ
| 0 _ _ := 0
| (n + 1) x y :=
  if x.head = y.head then
    hamming_distance x.tail y.tail
  else
    nat.succ (hamming_distance x.tail y.tail)


-- Example of this function in action using an alphabet of size 4
@[derive [decidable_eq, fintype]]
inductive 𝒟 : Type
| a : 𝒟
| b : 𝒟
| c : 𝒟
| d : 𝒟

open 𝒟

#eval hamming_distance ⟨[a,a,a,a], rfl⟩ ⟨[a,b,b,a], rfl⟩
#eval hamming_distance ⟨[a,b,c,d], rfl⟩ ⟨[d,c,b,a], rfl⟩
