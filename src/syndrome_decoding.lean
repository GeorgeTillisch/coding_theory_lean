import tactic
import binary
import hamming

structure BECC (n m d: ℕ) :=
  (encode : BW m → BW n)
  (decode : BW n → BW m)
  (error_count : BW n → BW n → ℕ)
  (error_correct : BW n → BW n)
  (error_correcting_code : 
    ∀ (msg : BW m) (received : BW n), 
      error_count (encode msg) received ≤ (d - 1)/2 → 
        decode (error_correct received) = msg)

namespace hamming_code

open B BW 

#eval ᴮ[O,O,O,O] ⬝ ᴮ[I,I,I,I] -- 0
#eval ᴮ[I,O,O,O] ⬝ ᴮ[I,O,O,I] -- 1

def G := ᴹ[
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


def R := ᴹ[
  ᴮ[O,O,I,O,O,O,O],
  ᴮ[O,O,O,O,I,O,O],
  ᴮ[O,O,O,O,O,I,O],
  ᴮ[O,O,O,O,O,O,I]
]

def decode (v: BW 7) : BW 4 := R × v

@[simp]
lemma decode_inverse_of_encode (msg : BW 4) : decode (encode msg) = msg :=
begin
  rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩,
  cases a; cases b; cases c; cases d; refl,
end


def H := ᴹ[
  ᴮ[I,O,I,O,I,O,I],
  ᴮ[O,I,I,O,O,I,I],
  ᴮ[O,O,O,I,I,I,I]
]

def syndrome_to_error_vector : BW 3 → BW 7
| ᴮ[O,O,O] := ᴮ[O,O,O,O,O,O,O]
| ᴮ[I,O,O] := ᴮ[I,O,O,O,O,O,O]
| ᴮ[O,I,O] := ᴮ[O,I,O,O,O,O,O]
| ᴮ[I,I,O] := ᴮ[O,O,I,O,O,O,O]
| ᴮ[O,O,I] := ᴮ[O,O,O,I,O,O,O]
| ᴮ[I,O,I] := ᴮ[O,O,O,O,I,O,O]
| ᴮ[O,I,I] := ᴮ[O,O,O,O,O,I,O]
| ᴮ[I,I,I] := ᴮ[O,O,O,O,O,O,I]

def error_correct (received : BW 7) : BW 7 := 
received - syndrome_to_error_vector (H × received)

meta def find_error : tactic unit :=
`[
  simp at *,
  cases received with _ hd tl, cases hd;
    {simp at h, rw h.symm, refl}
    <|>
    {cases tl with _ hd tl, cases hd;
      {simp at h, rw h.symm, refl}
      <|>
      {cases tl with _ hd tl, cases hd;
        {simp at h, rw h.symm, refl}
        <|>
        {cases tl with _ hd tl, cases hd;
          {simp at h, rw h.symm, refl}
          <|>
          {cases tl with _ hd tl, cases hd;
            {simp at h, rw h.symm, refl}
            <|>
            {cases tl with _ hd tl, cases hd;
              {simp at h, rw h.symm, refl}
              <|>
              {rcases tl with _ | ⟨_, hd, ⟨nil⟩⟩, cases hd; refl,},
            }
          }
        }
      }
    }
]

lemma single_error_correctable (msg : BW 4) (received : BW 7) : 
  d(encode msg, received) = 1 → error_correct received = encode msg := 
begin
  intro h,
  rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩,
  cases a; cases b; cases c; cases d; find_error,
end

lemma no_encoding_errors (msg : BW 4) : error_correct (encode msg) = encode msg :=
begin
  rw encode,
  rcases msg with _|⟨_,a,_|⟨_,b,_|⟨_,c,_|⟨_,d,⟨nil⟩⟩⟩⟩⟩,
  cases a; cases b; cases c; cases d; refl,
end

theorem one_error_correcting_code (msg : BW 4) (received : BW 7) : 
  d(encode msg, received) ≤ 1 → decode (error_correct received) = msg :=
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
    {have h₂ : encode msg = received,
    from hamming.distance_zero_eq (encode msg) received h₁,
    rw h₂.symm, 
    rw no_encoding_errors,
    rw decode_inverse_of_encode},
    {have h₂ : error_correct received = encode msg, 
    from single_error_correctable msg received h₁, 
    rw h₂, 
    rw decode_inverse_of_encode}
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