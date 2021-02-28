import tactic
import binary
import hamming

structure BECC (n m d: ℕ) :=
  (encode : BW m → BW n)
  (decode : BW n → BW m)
  (error_count : BW n → BW n → ℕ)
  (error_correct : BW n → BW n)
  (error_correcting_code : ∀ (msg : BW m) (received : BW n), error_count (encode msg) received ≤ (d - 1)/2 → decode (error_correct received) = msg)

namespace hamming_code

open B BW

def G := ᶜ[
  ᴮ[I,I,O,I],
  ᴮ[I,O,I,I],
  ᴮ[I,O,O,O],
  ᴮ[O,I,I,I],
  ᴮ[O,I,O,O],
  ᴮ[O,O,I,O],
  ᴮ[O,O,O,I]
]

def encode (u: BW 4) : BW 7 := G × u

@[simp]
def encOOOO : encode ᴮ[O,O,O,O] = ᴮ[O,O,O,O,O,O,O] := rfl
@[simp]
def encOOOI : encode ᴮ[O,O,O,I] = ᴮ[I,I,O,I,O,O,I] := rfl
@[simp]
def encOOIO : encode ᴮ[O,O,I,O] = ᴮ[O,I,O,I,O,I,O] := rfl
@[simp]
def encOOII : encode ᴮ[O,O,I,I] = ᴮ[I,O,O,O,O,I,I] := rfl
@[simp]
def encOIOO : encode ᴮ[O,I,O,O] = ᴮ[I,O,O,I,I,O,O] := rfl
@[simp]
def encOIOI : encode ᴮ[O,I,O,I] = ᴮ[O,I,O,O,I,O,I] := rfl
@[simp]
def encOIIO : encode ᴮ[O,I,I,O] = ᴮ[I,I,O,O,I,I,O] := rfl
@[simp]
def encOIII : encode ᴮ[O,I,I,I] = ᴮ[O,O,O,I,I,I,I] := rfl
@[simp]
def encIOOO : encode ᴮ[I,O,O,O] = ᴮ[I,I,I,O,O,O,O] := rfl
@[simp]
def encIOOI : encode ᴮ[I,O,O,I] = ᴮ[O,O,I,I,O,O,I] := rfl
@[simp]
def encIOIO : encode ᴮ[I,O,I,O] = ᴮ[I,O,I,I,O,I,O] := rfl
@[simp]
def encIOII : encode ᴮ[I,O,I,I] = ᴮ[O,I,I,O,O,I,I] := rfl
@[simp]
def encIIOO : encode ᴮ[I,I,O,O] = ᴮ[O,I,I,I,I,O,O] := rfl
@[simp]
def encIIOI : encode ᴮ[I,I,O,I] = ᴮ[I,O,I,O,I,O,I] := rfl
@[simp]
def encIIIO : encode ᴮ[I,I,I,O] = ᴮ[O,O,I,O,I,I,O] := rfl
@[simp]
def encIIII : encode ᴮ[I,I,I,I] = ᴮ[I,I,I,I,I,I,I] := rfl


def R := ᶜ[
  ᴮ[O,O,I,O,O,O,O],
  ᴮ[O,O,O,O,I,O,O],
  ᴮ[O,O,O,O,O,I,O],
  ᴮ[O,O,O,O,O,O,I]
]

def decode (v: BW 7) : BW 4 := R × v

@[simp]
lemma encode_decode_inverse (msg : BW 4) : decode (encode msg) = msg :=
begin
  rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩,
  cases a; cases b; cases c; cases d; refl,
end


def H := ᶜ[
  ᴮ[I,O,I,O,I,O,I],
  ᴮ[O,I,I,O,O,I,I],
  ᴮ[O,O,O,I,I,I,I]
]

@[simp]
def bw_len_3_to_nat_le_7 (v : BW 3) : v.to_nat ≤ 7 :=
begin
  rcases v with _|⟨_,a,_|⟨_,b,_|⟨_,c,⟨nil⟩⟩⟩⟩,
  cases a; cases b; cases c; 
    {repeat {rw BW.to_nat}, repeat {rw B.to_nat}, simp, try {linarith}}
end

def error_correct (v : BW 7) : BW 7 :=
let h : (H × v).reverse.to_nat ≤ 7 := by simp in v.flip (H × v).reverse.to_nat h


@[simp]
lemma no_encoding_errors (msg : BW 4) : error_correct (encode msg) = encode msg :=
begin
  rw encode,
  rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩,
  cases a; cases b; cases c; cases d; refl,
end

lemma distance_encoded_received_zero_eq (msg : BW 4) (received : BW 7) 
  : d(encode msg, received) = 0 → decode (error_correct received) = msg := 
begin
  intro h_d_zero,
  have h_eq : encode msg = received, from hamming.distance_zero_eq (encode msg) received h_d_zero,
  rw h_eq.symm,
  simp,
end


meta def find_bit_flip : tactic unit :=
`[
  cases received with _ hd tl, cases hd;
    {simp at h, rw h, use [1, ⟨by linarith, by simp⟩], refl}
    <|>
    {cases tl with _ hd tl, cases hd;
      {simp at h, rw h,use [2, ⟨by linarith, by simp⟩], refl}
      <|>
      {cases tl with _ hd tl, cases hd;
        {simp at h, rw h,use [3, ⟨by linarith, by simp⟩], refl}
        <|>
        {cases tl with _ hd tl, cases hd;
          {simp at h, rw h,use [4, ⟨by linarith, by simp⟩], refl}
          <|>
          {cases tl with _ hd tl, cases hd;
            {simp at h, rw h,use [5, ⟨by linarith, by simp⟩], refl}
            <|>
            {cases tl with _ hd tl, cases hd;
              {simp at h, rw h,use [6, ⟨by linarith, by simp⟩], refl}
              <|>
              {rcases tl with _ | ⟨_, hd, ⟨nil⟩⟩, cases hd;
                {use [7, ⟨by linarith, by simp⟩], refl}
                <|>
                {simp at h, exfalso, exact h},
              },
            }
          }
        }
      }
    }
]

lemma distance_OOOO_received_one_bit_flip (received : BW 7)  (h : d(encode ᴮ[O,O,O,O], received) = 1)
  : ∃ (x : ℕ) (hx: 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,O,O,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_OOOI_received_one_bit_flip (received : BW 7)  (h : d(encode ᴮ[O,O,O,I], received) = 1)
  : ∃ (x : ℕ) (hx: 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,O,O,I]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_OOIO_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[O,O,I,O], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,O,I,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_OOII_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[O,O,I,I], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,O,I,I]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_OIOO_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[O,I,O,O], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,I,O,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_OIOI_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[O,I,O,I], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,I,O,I]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_OIIO_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[O,I,I,O], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,I,I,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_OIII_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[O,I,I,I], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[O,I,I,I]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IOOO_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,O,O,O], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,O,O,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IOOI_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,O,O,I], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,O,O,I]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IOIO_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,O,I,O], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,O,I,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IOII_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,O,I,I], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,O,I,I]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IIOO_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,I,O,O], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,I,O,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IIOI_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,I,O,I], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,I,O,I]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IIIO_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,I,I,O], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,I,I,O]).flip x hx.right :=
by {simp at *, find_bit_flip}
lemma distance_IIII_received_one_bit_flip (received : BW 7) (h : d(encode ᴮ[I,I,I,I], received) = 1)
  : ∃ (x : ℕ) (hx : 1 ≤ x ∧ x ≤ 7), received = (encode ᴮ[I,I,I,I]).flip x hx.right :=
by {simp at *, find_bit_flip}

lemma distance_encoded_received_one_bit_flip (msg : BW 4) (received : BW 7) 
  : d(encode msg, received) = 1 → ∃ (x : ℕ) (h: 1 ≤ x ∧ x ≤ 7), received = (encode msg).flip x h.right :=
begin
  intro h,
  rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩,
  cases a; cases b; cases c; cases d;
  {apply distance_OOOO_received_one_bit_flip, exact h}
  <|>
  {apply distance_OOOI_received_one_bit_flip, exact h}
  <|>
  {apply distance_OOIO_received_one_bit_flip, exact h}
  <|>
  {apply distance_OOII_received_one_bit_flip, exact h}
  <|>
  {apply distance_OIOO_received_one_bit_flip, exact h}
  <|>
  {apply distance_OIOI_received_one_bit_flip, exact h}
  <|>
  {apply distance_OIIO_received_one_bit_flip, exact h}
  <|>
  {apply distance_OIII_received_one_bit_flip, exact h}
  <|>
  {apply distance_IOOO_received_one_bit_flip, exact h}
  <|>
  {apply distance_IOOI_received_one_bit_flip, exact h}
  <|>
  {apply distance_IOIO_received_one_bit_flip, exact h}
  <|>
  {apply distance_IOII_received_one_bit_flip, exact h}
  <|>
  {apply distance_IIOO_received_one_bit_flip, exact h}
  <|>
  {apply distance_IIOI_received_one_bit_flip, exact h}
  <|>
  {apply distance_IIIO_received_one_bit_flip, exact h}
  <|>
  {apply distance_IIII_received_one_bit_flip, exact h}
end

@[simp]
lemma H_mul_flipped_i_gives_i (msg : BW 4) (i : ℕ) (h: i ≤ 7) 
  : (H × flip i h (encode msg)).reverse.to_nat = i :=
begin
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i;
    -- 1 ≤ 0 ≤ 7
    {rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩, cases a; cases b; cases c; cases d; refl,}
    <|>
    -- i > 7
    {have : i.succ.succ.succ.succ.succ.succ.succ.succ = i + 8, by refl,
    rw this at h,
    have : 8 ≥ 7, by norm_num,
    exfalso, 
    linarith}
end

@[simp]
lemma flip_flipped_bit_gives_original (msg : BW 4) (i : ℕ) (h: i ≤ 7)
  : flip i h (flip i h (encode msg)) = encode msg :=
begin
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i;
    -- i = 0
    refl
    -- 1 ≤ i ≤ 7
    <|>
    {rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩, cases a; cases b; cases c; cases d; refl,}
    <|>
    -- i > 7
    {have : i.succ.succ.succ.succ.succ.succ.succ.succ = i + 8, by refl,
    rw this at h,
    have : 8 ≥ 7, by norm_num,
    exfalso, 
    linarith}
end

lemma error_correct_flip_gives_original (msg : BW 4) (received : BW 7) (i : ℕ) (h: 1 ≤ i ∧ i ≤ 7)
  : error_correct ((encode msg).flip i h.right) = encode msg :=
begin
  unfold error_correct,
  simp,
end


lemma single_error_correctable (msg : BW 4) (received : BW 7) 
  : d(encode msg, received) = 1 → error_correct received = encode msg := 
begin
  intro h,
  have h' : ∃ (i : ℕ) (h: 1 ≤ i ∧ i ≤ 7), received = (encode msg).flip i h.right,
  from distance_encoded_received_one_bit_flip msg received h,
  rcases h' with ⟨i, h_i, h_flip⟩,
  rw h_flip,
  rw error_correct_flip_gives_original,
  exact received,
end

lemma distance_encoded_received_one_eq (msg : BW 4) (received : BW 7) : d(encode msg, received) = 1 → decode (error_correct received) = msg := 
begin
  intro h,
  have h₁ : error_correct received = encode msg, 
  from single_error_correctable msg received h,
  rw h₁,
  simp,
end

theorem one_error_correcting_code (msg : BW 4) (received : BW 7) : d(encode msg, received) ≤ 1 → decode (error_correct received) = msg :=
begin
  intro h,
  have h₁ : d(encode msg, received) = 0 ∨ d(encode msg, received) = 1,
    {cases d(encode msg, received) with n h,
      {left, refl},
      {right,
      have n_succ_ne_zero : ¬n.succ = 0, from nat.succ_ne_zero n,
      have n_succ_gt_zero : n.succ > 0, from nat.pos_of_ne_zero n_succ_ne_zero,
      linarith}
    },
  cases h₁,
    {apply distance_encoded_received_zero_eq, exact h₁},
    {apply distance_encoded_received_one_eq, exact h₁}
end

def hamming74code : BECC 7 4 3 :=
{
  encode := hamming_code.encode,
  decode := hamming_code.decode,
  error_count := hamming.distance,
  error_correct := hamming_code.error_correct,
  error_correcting_code := hamming_code.one_error_correcting_code,
}

end hamming_code