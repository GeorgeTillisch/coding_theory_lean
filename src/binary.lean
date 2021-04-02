import tactic
import data.fintype.card

@[derive decidable_eq]
inductive B : Type
| O : B
| I : B

namespace B

instance : fintype B := 
{
  elems := {O, I},
  complete := by {intro x, simp, cases x, {left, refl}, {right, refl}} 
}
@[simp]
lemma card_b : fintype.card B = 2 := rfl

def repr : B → string
| O := "0"
| I := "1"
instance : has_repr B := ⟨repr⟩

@[simp]
lemma O_ne_I : O = I → false :=
λ h, by contradiction
@[simp]
lemma I_ne_O : I = O → false :=
λ h, by contradiction

def add : B → B → B
| I I := O
| O x := x
| x O := x

def mul : B → B → B
| I I := I
| _ _ := O

instance : field B := 
{
  add := add,
  add_assoc := λ a b c, by {cases a; cases b; cases c; refl},
  zero := O,
  zero_add := λ a, by {cases a; refl},
  add_zero := λ a, by {cases a; refl},
  neg := λ x, x,
  sub := λ x, add x,
  sub_eq_add_neg := λ a b, rfl,
  add_left_neg := λ a, by {cases a; refl},
  add_comm := λ a b, by {cases a; cases b; refl},
  mul := mul,
  mul_assoc := λ a b c, by {cases a; cases b; cases c; refl},
  one := I,
  one_mul := λ a, by {cases a; refl},
  mul_one := λ a, by {cases a; refl},
  left_distrib :=  λ a b c, by {cases a; cases b; cases c; refl},
  right_distrib :=  λ a b c, by {cases a; cases b; cases c; refl},
  mul_comm :=  λ a b, by {cases a; cases b; refl},
  inv := λ x, x,
  exists_pair_ne := ⟨O, ⟨I, O_ne_I⟩⟩,
  mul_inv_cancel := begin
    intros a h,
    cases a,
      {contradiction},
      {refl}
  end,
  inv_zero := rfl,
}

def flip : B → B
| O := I
| I := O

def to_nat : B → ℕ
| O := 0
| I := 1

end B

@[derive decidable_eq]
inductive BW : ℕ → Type
| nil : BW nat.zero
| cons {n : ℕ} (b : B) (bw : BW n) : BW (n + 1)

namespace BW
open B

notation h `::ᴮ` t := cons h t
notation `ᴮ[` bw:(foldr `,` (h t, cons h t) nil) `]` := bw

def repr : Π {n : ℕ}, BW n → string
| _   nil         := ""
| _   (hd ::ᴮ tl)  := hd.repr ++ (repr tl)
instance {n : ℕ} : has_repr (BW n) := ⟨BW.repr⟩

def length : Π {n : ℕ}, BW n → ℕ
| n _ := n

@[simp]
lemma nil_unique (x : BW 0) : x = BW.nil := by {cases x; refl}

private
def reverse' : Π {n i : ℕ}, BW n → BW i → BW (n + i)
| 0 i nil acc := by {simp, exact acc}
| (m+1) i (hd::ᴮtl) acc := by {rw nat.add_assoc, rw nat.one_add, apply reverse' tl (hd::ᴮacc)}

def reverse : Π {n : ℕ}, BW n → BW n := λ (n : ℕ) (bwn : BW (n - 0)), reverse' bwn nil

def add : Π {n : ℕ}, BW n → BW n → BW n
| _ nil nil := nil
| _ (hd₁::ᴮtl₁) (hd₂::ᴮtl₂) := (hd₁ + hd₂) ::ᴮ (add tl₁ tl₂)

def intersection : Π {n : ℕ}, BW n → BW n → BW n
| _ nil nil := nil
| _ (hd₁::ᴮtl₁) (hd₂::ᴮtl₂) := (hd₁ * hd₂) ::ᴮ (intersection tl₁ tl₂)

notation bw₁ `∩` bw₂ := intersection bw₁ bw₂

def dot_product :  Π {n : ℕ}, BW n → BW n → B
| _ nil nil := O
| _ (hd₁::ᴮtl₁) (hd₂::ᴮtl₂) := (hd₁ * hd₂) + (dot_product tl₁ tl₂)

notation bw₁ `⬝` bw₂ := dot_product bw₁ bw₂


def zero : Π (n : ℕ), BW n
| 0       := nil
| (m + 1) := O ::ᴮ zero m


def to_nat : Π {n : ℕ}, BW n → ℕ
| _     nil       := 0
| (m+1) (hd::ᴮtl) := (hd.to_nat * 2 ^ m) + tl.to_nat


def flip : Π {n : ℕ} (i : ℕ), i ≤ n → BW n → BW n
| _ _ _ nil := nil
| _ 0 _ (hd::ᴮtl) := hd ::ᴮ tl
| _ 1 _ (hd::ᴮtl) := hd.flip ::ᴮ tl
| _ (i+1) h (hd::ᴮtl) := hd ::ᴮ (flip i (nat.le_of_succ_le_succ h) tl)

@[simp]
lemma add_hds {n : ℕ} (hd₁ hd₂ : B) (tl₁ tl₂ : BW n) 
  : add (hd₁::ᴮtl₁) (hd₂::ᴮtl₂) = ((hd₁ + hd₂)::ᴮ(add tl₁ tl₂)) :=
rfl

instance : Π {n : ℕ}, add_comm_group (BW n) := 
λ n, {
  add := add,
  add_assoc := begin
    intros a b c,
    induction a with m hda tla ih,
      {rw nil_unique b, rw nil_unique c, refl},
    cases b with _ hdb tlb,
    cases c with _ hdc tlc,
    simp,
    split,
      {conv {to_lhs, apply_congr add_assoc}},
      {simp at ih, apply ih}
  end,
  zero := zero n,
  zero_add := begin
    intro a, 
    induction a with m hda tla ih,
      {refl},
    simp at *, rw zero,
    cases hda;
      {conv {to_lhs, apply_congr add_hds}, conv {to_lhs, congr, {whnf}, {apply_congr ih}}},
  end,
  add_zero := begin
    intro a, 
    induction a with m hda tla ih,
      {refl},
    simp at *, rw zero,
    cases hda;
      {conv {to_lhs, apply_congr add_hds}, conv {to_lhs, congr, {whnf}, {apply_congr ih}}},
  end,
  neg := λ x, x,
  sub := λ x, add x,
  sub_eq_add_neg := λ x y, rfl,
  add_left_neg := begin
    intro a,
    induction a with m hda tla ih,
      {refl},
    conv {to_lhs, apply_congr add_hds},
    conv {to_lhs, congr, skip, apply_congr ih},
    cases hda; refl,
  end,
  add_comm := begin
    intros a b,
    induction a with m hda tla ih,
      {rw nil_unique b,},
    cases b with _ hdb tlb,
    cases hda; cases hdb;
    {conv {to_lhs, apply_congr add_hds},
    conv {to_lhs, congr, {whnf}, {apply_congr ih}},
    conv {to_rhs, apply_congr add_hds},
    conv {to_rhs, congr, {whnf}},
    refl}
  end,
}

def smul : Π {n : ℕ}, B → BW n → BW n
| _ _ nil := nil
| _ b (hd::ᴮtl) := (b * hd)::ᴮ(smul b tl)

instance : Π {n : ℕ}, vector_space B (BW n) :=
λ n, {
  smul := smul,
  one_smul := begin
    intro b,
    induction b with m hdb tlb ih,
      {refl},
    simp, rw smul,
    conv {to_lhs, congr, skip, apply_congr ih},
    cases hdb; refl,
  end,
  mul_smul := begin
    intros x y b,
    induction b with m hdb tlb ih,
      {refl},
    simp, rw smul,
    conv {to_lhs, congr, skip, apply_congr ih},
    cases x; cases y; cases hdb; refl,
  end,
  smul_add := begin
    intros r x y,
    induction y with m hdy tly ih,
      {rw nil_unique x, refl},
    cases x with _ hdx tlx,
    simp,
    conv {to_lhs, congr, skip, apply_congr add_hds},
    rw smul,
    conv {to_lhs, congr, skip, apply_congr ih},
    cases r; cases hdx; cases hdy; refl,
  end,
  smul_zero := begin
    intro r,
    simp,
    induction n with m ih,
      {refl},
    conv {to_lhs, whnf, congr, skip, apply_congr ih},
    cases r; refl,
  end,
  add_smul := begin
    intros r s x,
    induction x with m hdx tlx ih,
      {refl},
    simp, rw smul,
    conv {to_lhs, congr, skip, apply_congr ih},
    cases r; cases s; cases hdx; refl,
  end,
  zero_smul := begin
    intro x,
    induction x with m hdx tlx ih,
      {refl},
    simp, rw smul,
    conv {to_lhs, congr, skip, apply_congr ih},
    cases hdx; refl,
  end,
}

def vector_to_bw : Π {n : ℕ}, vector B n → BW n
| 0     ⟨[],     _⟩ := nil
| (n+1) ⟨hd::tl, h⟩ := cons hd (vector_to_bw ⟨tl, by {simp at h, exact h}⟩)

lemma vector_to_bw_injective : Π {n : ℕ}, function.injective (@vector_to_bw n) :=
begin
  intros n x y h,
  induction n with k ih,
    {simp},
  cases x with xl hx,
  cases xl with xhd xtl,
    {simp at hx, contradiction},
  cases y with yl hy,
  cases yl with yhd ytl,
    {simp at hy, contradiction},
  repeat {rw vector_to_bw at h}, 
  simp at h, cases h with h_left h_right, rw h_left,
  simp, specialize ih h_right, simp at ih, exact ih,
end

lemma vector_to_bw_surjective : Π {n : ℕ}, function.surjective (@vector_to_bw n) :=
begin
  intros n b,
  induction n with k ih,
    {use vector.nil, rw nil_unique b, refl},
  cases b with _ bhd btl,
  specialize ih btl,
  cases ih with a_ih ih,
  cases a_ih with al_ih h_a_ih,
  have : (bhd::al_ih).length = k.succ, by {rw list.length_cons, rw h_a_ih},
  use ⟨bhd::al_ih, this⟩,
  rw vector_to_bw, simp, exact ih,
end

lemma vector_to_bw_bijective : Π {n : ℕ}, function.bijective (@vector_to_bw n) :=
λ n, ⟨vector_to_bw_injective, vector_to_bw_surjective⟩

instance : Π {n : ℕ}, fintype (BW n) :=
λ n, fintype.of_bijective vector_to_bw vector_to_bw_bijective

def bw_to_vector : Π {n : ℕ}, BW n → vector B n
| 0     nil       := vector.nil
| (n+1) (hd::ᴮtl) := hd ::ᵥ bw_to_vector tl

def bw_to_vector_inv : Π {n : ℕ}, vector B n → BW n
| 0     _ := nil
| (n+1) v := (vector.head v) ::ᴮ (bw_to_vector_inv (vector.tail v))

lemma left_inv : 
  Π {n : ℕ} (x : BW n), bw_to_vector_inv (bw_to_vector x) = x
| 0     nil       := by rw [bw_to_vector, bw_to_vector_inv]
| (n+1) (hd::ᴮtl) := by {rw [bw_to_vector, bw_to_vector_inv], simp, exact left_inv tl}

lemma right_inv :
  Π {n : ℕ} (x : vector B n), bw_to_vector (bw_to_vector_inv x) = x
| 0     v := by rw [bw_to_vector_inv, bw_to_vector, vector.eq_nil v]
| (n+1) v := by rw [bw_to_vector_inv, bw_to_vector, right_inv v.tail, vector.cons_head_tail]

def vector_bw_equiv : Π {n : ℕ}, equiv (BW n) (vector B n) :=
λ n, 
{
  to_fun := bw_to_vector,
  inv_fun := bw_to_vector_inv,
  left_inv := left_inv,
  right_inv := right_inv,
}

lemma card_bw_eq_card_vector {n : ℕ} : fintype.card (BW n) = fintype.card (vector B n) :=
by {apply fintype.card_congr, exact vector_bw_equiv}

@[simp]
lemma card_bw {n : ℕ} : fintype.card (BW n) = 2 ^ n :=
by {rw card_bw_eq_card_vector, simp}

end BW


inductive BWM (n : ℕ) : ℕ → Type
| nil : BWM nat.zero
| cons {m : ℕ} (bw : BW n) (bc : BWM m) : BWM m.succ

namespace BWM

notation h`::ᶜ` t := cons h t
notation `ᶜ[` bc:(foldr `,` (h t, cons h t) nil) `]` := bc

def repr : Π {n m : ℕ}, BWM n m → string
| _ _ nil       := ""
| _ _ (hd::ᶜtl) := hd.repr ++ "\n" ++ (repr tl)
instance {n m : ℕ} : has_repr (BWM n m) := ⟨BWM.repr⟩

def length : Π {n m : ℕ}, BWM n m → ℕ
| n _ _ := n

def size : Π {n m : ℕ}, BWM n m → ℕ
| _ m _ := m

def r_mul : Π {n m : ℕ}, BWM n m → BW n → BW m
| _ 0 BWM.nil _ := BW.nil
| n m (hd::ᶜtl) bw := (hd ⬝ bw)::ᴮ(r_mul tl bw)

notation bc `×` bw := r_mul bc bw

end BWM