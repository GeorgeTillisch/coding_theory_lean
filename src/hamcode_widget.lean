import binary
import syndrome_decoding
open B BW
open hamming_code
open widget


/-!
# A widget for expoloring the Hamming(7,4) code.

Requires Lean extension for VSCode.
Click on the `#html` command to see the widget in the infoview panel.
(The widget looks best on a dark theme)
-/

variables {π α : Type}

def get_ith : Π {n : ℕ} (i : ℕ), BW n → string
| 0 _     _         := "" 
| _ 1     (hd::ᴮtl) := hd.repr
| _ (i+1) (hd::ᴮtl) := get_ith i tl

def flip' : Π {n : ℕ} (i : ℕ), BW n → BW n
| 0 _     x         := x
| _ 1     (hd::ᴮtl) := hd.flip ::ᴮ tl
| _ (i+1) (hd::ᴮtl) := hd ::ᴮ (flip' i tl)

inductive hamcode_action
| flip_first | flip_second | flip_third | flip_fourth
| pos1 | pos2 | pos3 | pos4 | pos5 | pos6 | pos7

open hamcode_action

meta def hamcode_init : π → (BW 4) × ℕ
| _ := ⟨ᴮ[O,O,O,O], 0⟩

meta def hamcode_props_changed : π → π → (BW 4) × ℕ → (BW 4) × ℕ
| _ _ word_and_errpos := word_and_errpos

meta def hamcode_update : π → (BW 4) × ℕ → hamcode_action → ((BW 4) × ℕ) × option α
| _ ⟨x, errpos⟩ flip_first  := ⟨⟨x.flip 1 (by simp), errpos⟩, none⟩
| _ ⟨x, errpos⟩ flip_second := ⟨⟨x.flip 2 (by simp), errpos⟩, none⟩
| _ ⟨x, errpos⟩ flip_third  := ⟨⟨x.flip 3 (by simp), errpos⟩, none⟩
| _ ⟨x, errpos⟩ flip_fourth := ⟨⟨x.flip 4 (by simp), errpos⟩, none⟩
| _ ⟨x, errpos⟩ pos1        := ⟨⟨x, 1⟩, none⟩
| _ ⟨x, errpos⟩ pos2        := ⟨⟨x, 2⟩, none⟩
| _ ⟨x, errpos⟩ pos3        := ⟨⟨x, 3⟩, none⟩
| _ ⟨x, errpos⟩ pos4        := ⟨⟨x, 4⟩, none⟩
| _ ⟨x, errpos⟩ pos5        := ⟨⟨x, 5⟩, none⟩
| _ ⟨x, errpos⟩ pos6        := ⟨⟨x, 6⟩, none⟩
| _ ⟨x, errpos⟩ pos7        := ⟨⟨x, 7⟩, none⟩

meta def hamcode_view : (((BW 4) × ℕ) × π) → list (html hamcode_action)
| ⟨⟨x, errpos⟩, _⟩ :=
  h "section" [className "mw5 mw7-ns center bg-transparent pa3 ph5-ns"] [
    h "h2" [className "mt0"] ["The Hamming(7,4) Code"],
    h "p" [className "lh-copy measure"] ["Click on bits of the message to flip them. Click on error positions to flip a bit in the received word."],
    h "h3" [] ["Message:"],
    h "div" [className "dtc code"] [
      h "button" [className "f3 br2 ph3 pv2 mb2 dib blue bg-white", on_click (λ ⟨⟩, flip_first)] 
                [get_ith 1 x],
      h "button" [className "f3 br2 ph3 pv2 mb2 dib blue bg-white", on_click (λ ⟨⟩, flip_second)] 
                [get_ith 2 x],
      h "button" [className "f3 br2 ph3 pv2 mb2 dib blue bg-white", on_click (λ ⟨⟩, flip_third)] 
                [get_ith 3 x],
      h "button" [className "f3 br2 ph3 pv2 mb2 dib blue bg-white", on_click (λ ⟨⟩, flip_fourth)] 
                [get_ith 4 x]
    ],
    h "h3" [] ["Encoded Word:"],
    h "div" [className "dtc code"] [
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib green bg-white"] 
        [get_ith 1 (hamming74code.encode x)],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib green bg-white"] 
        [get_ith 2 (hamming74code.encode x)],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib blue bg-white"] 
        [get_ith 3 (hamming74code.encode x)],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib green bg-white"] 
        [get_ith 4 (hamming74code.encode x)],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib blue bg-white"] 
        [get_ith 5 (hamming74code.encode x)],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib blue bg-white"] 
        [get_ith 6 (hamming74code.encode x)],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib blue bg-white"] 
        [get_ith 7 (hamming74code.encode x)]
    ],
    h "h3" [className "dib mr2"] ["Error Position"], html.of_string $ to_string $ errpos, 
    h "div" [className "dtc code"] [
      h "button" [className "f3 dim br2 ph3 pv2 mb2 dib bg-white", on_click (λ ⟨⟩, pos1)] ["_"],
      h "button" [className "f3 dim br2 ph3 pv2 mb2 dib bg-white", on_click (λ ⟨⟩, pos2)] ["_"],
      h "button" [className "f3 dim br2 ph3 pv2 mb2 dib bg-white", on_click (λ ⟨⟩, pos3)] ["_"],
      h "button" [className "f3 dim br2 ph3 pv2 mb2 dib bg-white", on_click (λ ⟨⟩, pos4)] ["_"],
      h "button" [className "f3 dim br2 ph3 pv2 mb2 dib bg-white", on_click (λ ⟨⟩, pos5)] ["_"],
      h "button" [className "f3 dim br2 ph3 pv2 mb2 dib bg-white", on_click (λ ⟨⟩, pos6)] ["_"],
      h "button" [className "f3 dim br2 ph3 pv2 mb2 dib bg-white", on_click (λ ⟨⟩, pos7)] ["_"]
    ],
    h "h3" [] ["Received Word:"],
    h "div" [className "dtc code"] [
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 1 (flip' errpos (hamming74code.encode x))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 2 (flip' errpos (hamming74code.encode x))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 3 (flip' errpos (hamming74code.encode x))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 4 (flip' errpos (hamming74code.encode x))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 5 (flip' errpos (hamming74code.encode x))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 6 (flip' errpos (hamming74code.encode x))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 7 (flip' errpos (hamming74code.encode x))]
    ],
    h "h3" [] ["Syndrome:"],
    h "div" [className "dtc code"] [
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 1 (H × (flip' errpos (hamming74code.encode x))).reverse],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"]
        [get_ith 2 (H × (flip' errpos (hamming74code.encode x))).reverse],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"]
        [get_ith 3 (H × (flip' errpos (hamming74code.encode x))).reverse]
    ],
    h "h3" [] ["Corrected Word:"],
    h "div" [className "dtc code"] [
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 1 (hamming74code.error_correct (flip' errpos (hamming74code.encode x)))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 2 (hamming74code.error_correct (flip' errpos (hamming74code.encode x)))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 3 (hamming74code.error_correct (flip' errpos (hamming74code.encode x)))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 4 (hamming74code.error_correct (flip' errpos (hamming74code.encode x)))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 5 (hamming74code.error_correct (flip' errpos (hamming74code.encode x)))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 6 (hamming74code.error_correct (flip' errpos (hamming74code.encode x)))],
      h "div" [className "f3 br2 ph3 pv2 mb2 mr1 dib black bg-white"] 
        [get_ith 7 (hamming74code.error_correct (flip' errpos (hamming74code.encode x)))]
    ]
  ]

meta def HamcodeDemo : component π α :=
component.with_state
  hamcode_action
  ((BW 4) × ℕ) 
  hamcode_init
  hamcode_props_changed
  hamcode_update
$ component.pure hamcode_view

-- Click on the #html part to see the widget
#html HamcodeDemo