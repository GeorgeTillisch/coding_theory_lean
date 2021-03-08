import tactic
import binary
import hamming
import algebra.module.submodule

open B BW

structure binary_linear_code (n m d : ℕ) :=
  (cws : finset (BW n))
  (card_gte : cws.card ≥ 2)
  (is_subspace : subspace B (BW n))

namespace binary_linear_code

instance : Π {n m d : ℕ}, has_mem (BW n) (binary_linear_code n m d) :=
λ n m d, ⟨λ (x : BW n), λ (C : binary_linear_code n m d), x ∈ C.cws⟩

def min_distance {n m d : ℕ} (C : binary_linear_code n m d) : ℕ :=
  finset.min' (finset.image (λ (x : BW n × BW n), d(x.fst, x.snd)) C.cws.off_diag)
  begin
    have : ∃ (x y : BW n), x ∈ C ∧ y ∈ C ∧ x ≠ y, 
    from finset.one_lt_card_iff.mp C.card_gte,
    simp, rw finset.nonempty, simp,
    rcases this with ⟨x, y, ⟨hx, hy, hxy⟩⟩,
    existsi [x, hx, y, hy],
    exact hxy,
  end

notation `d(` C `)` := min_distance C

variables {n m d : ℕ} {C : binary_linear_code n m d}

lemma dist_neq_codewords_gt_min_distance:
  ∀ (c₁ c₂ ∈ C), c₁ ≠ c₂ → d(C) ≤ d(c₁,c₂):=
begin
  intros c₁ c₂ hc₁ hc₂ hneq,
  unfold min_distance,
  apply finset.min'_le,
  simp,
  existsi [c₁, c₂],
  exact ⟨⟨hc₁, hc₂, hneq⟩, rfl⟩,
end

lemma min_distance_pair : ∃ (c₁ c₂ ∈ C), c₁ ≠ c₂ ∧ d(c₁,c₂) = d(C) :=
begin
  have h_mem : d(C) ∈ (finset.image (λ (x : BW n × BW n), d(x.fst, x.snd)) C.cws.off_diag),
  by {rw min_distance, apply finset.min'_mem},
  simp at h_mem,
  rcases h_mem with ⟨x, y, ⟨hx, hy, hneq⟩, h_dist⟩,
  existsi [x, y, hx, hy],
  exact ⟨hneq, h_dist⟩,
end

theorem s_error_detecting_iff_min_distance_gt_s (s : ℕ) : 
  (∀ (x : BW n) (c ∈ C), d(x,c) ≥ 1 ∧ d(x,c) ≤ s → x ∉ C) ↔ d(C) > s :=
begin
  split,
    {contrapose,
    simp,
    intro h_min_dist,
    have : ∃ (c₁ c₂ ∈ C), c₁ ≠ c₂ ∧ d(c₁,c₂) = d(C), from min_distance_pair,
    rcases this with ⟨x, y, hx, hy, ⟨hneq, h_dist_eq_min⟩⟩,
    have h_lte_s : d(x,y) ≤ s, by linarith,
    have h_gte_1 : d(x,y) ≥ 1, from (hamming.distance_neq_between_one_n x y hneq).left,
    existsi [x, y],
    exact ⟨hy, h_gte_1, h_lte_s, hx⟩,
    },
    {intros h x c hc hdist,
    intro hx,
    by_cases heq : x = c,
      {have h_dxc_eq_zero : d(x,c) = 0, from hamming.eq_distance_zero x c heq,
      linarith},
      {have : d(x,c) ≥ d(C), 
      from dist_neq_codewords_gt_min_distance x c hx hc heq,
      linarith,}
    },
end


def change_t_disagreements : Π {n : ℕ}, ℕ → BW n → BW n → BW n
| _ _     nil         nil       := nil
| _ 0     (xhd::ᴮxtl) (_::ᴮytl) := xhd::ᴮxtl
| _ t     (O::ᴮxtl)   (O::ᴮytl) :=   O::ᴮ(change_t_disagreements t xtl ytl)
| _ t     (I::ᴮxtl)   (I::ᴮytl) :=   I::ᴮ(change_t_disagreements t xtl ytl)
| _ (t+1) (O::ᴮxtl)   (I::ᴮytl) :=   I::ᴮ(change_t_disagreements t xtl ytl)
| _ (t+1) (I::ᴮxtl)   (O::ᴮytl) :=   O::ᴮ(change_t_disagreements t xtl ytl)

lemma dist_change_t_disagreements_first_arg : 
  Π {n : ℕ} (t : ℕ) (h₁ : 0 < t) (x y : BW n) (h₂ : t < d(x,y)), 
  d(x, change_t_disagreements t x y) = t
| n t     h₁ nil         nil         h₂ := by {exfalso, simp at h₂, contradiction}
| n 0     h₁ (xhd::ᴮxtl) (yhd::ᴮytl) h₂ := by {exfalso, simp at h₁, contradiction}
| n (t+1) h₁ (xhd::ᴮxtl) (yhd::ᴮytl) h₂ := 
  begin
    cases xhd; cases yhd;
      begin
      rw change_t_disagreements, simp, simp at h₂,
      apply dist_change_t_disagreements_first_arg (t+1) h₁ xtl ytl h₂,
      end
      <|>
      begin
      rw change_t_disagreements, simp,
      rw ← nat.add_one, simp,
      simp at h₂, have h₃ : t < d(xtl,ytl), from nat.lt_of_succ_lt_succ h₂,
      cases t,
        {simp, cases xtl with _ xhd xtl,
          {rw nil_unique ytl, rw change_t_disagreements},
        cases ytl with _ yhd ytl, cases xhd; cases yhd; rw change_t_disagreements,
        },
      have h₅ : 0 < t.succ, from nat.zero_lt_succ t,
      apply dist_change_t_disagreements_first_arg (t+1) h₅ xtl ytl h₃,
      end
  end

lemma dist_change_t_disagreements_second_arg : 
  Π {n : ℕ} (t : ℕ) (x y : BW n), d(y, change_t_disagreements t x y) = d(x,y) - t 
| n t     nil         nil         := by {simp, cases t; rw change_t_disagreements}
| n 0     (xhd::ᴮxtl) (yhd::ᴮytl) := 
  begin
  cases xhd; cases yhd; 
    {rw change_t_disagreements, simp, apply hamming.distance_symmetric}
  end
| n (t+1) (xhd::ᴮxtl) (yhd::ᴮytl) := 
  begin
  cases xhd; cases yhd; 
    {rw change_t_disagreements, simp, apply dist_change_t_disagreements_second_arg}
  end

theorem t_error_correcting_iff_min_distance_gte (t : ℕ) :
  (∀ (c ∈ C) (x : BW n), (d(x,c) ≤ t → (∀ (c' ∈ C), c ≠ c' → d(x,c) < d(x,c'))))
    ↔ d(C) ≥ 2 * t + 1 :=
begin
  split,
    {intro h₁,
    by_contradiction h₂,
    simp at h₂,
    have h₃ : ∃ (c₁ c₂ ∈ C), c₁ ≠ c₂ ∧ d(c₁,c₂) = d(C),
    from min_distance_pair,
    rcases h₃ with ⟨c, c', hc, hc', ⟨hneq, h_dist_eq_min⟩⟩,
    have h₄ : d(c,c') ≤ 2 * t, by linarith,
    have h₅ : d(c, c') ≥ t + 1, 
    by {
      specialize h₁ c hc c',
      by_contradiction h',
      simp at h',
      have h'' : d(c,c') ≤ t, from nat.le_of_lt_succ h',
      rw hamming.distance_symmetric at h'',
      specialize h₁ h'' c' hc' hneq,
      have : d(c',c') = 0, from hamming.eq_distance_zero c' c' rfl,
      rw this at h₁,
      simp at h₁,
      exact h₁,
    },
    have h₆ : ∃ (x : BW n), 1 ≤ d(x,c') ∧ d(x,c') ≤ d(x,c) ∧ d(x,c) = t,
    by {
      use change_t_disagreements t c c',
      have h_d₀ : 1 ≤ d(c,c') ∧ d(c,c') ≤ n, from hamming.distance_neq_between_one_n c c' hneq,
      have h_d₁ : d(c, change_t_disagreements t c c') = t,
      by {apply dist_change_t_disagreements_first_arg; linarith},
      have h_d₂ : d(c', change_t_disagreements t c c') = d(c,c') - t,
      by {apply dist_change_t_disagreements_second_arg},
      rw [hamming.distance_symmetric _ c, hamming.distance_symmetric _ c'],
      split,
        {calc d(c',change_t_disagreements t c c') ≥ d(c,c') - t : by linarith
        ...                                       ≥ t + 1 - t   : by exact nat.sub_le_sub_right h₅ t
        ...                                       = 1           : by simp,},
        split,
        {rw [h_d₁, h_d₂], 
        apply nat.sub_le_left_iff_le_add.mpr,
        conv {congr, skip, ring},
        exact h₄,},
        {linarith}
    },
    rcases h₆ with ⟨x, ⟨h_dxgt1, h_dxc'_le_dxc, h_dxc_eq_t⟩⟩,
    have h_dxc_le_t : d(x,c) ≤ t, by linarith,
    specialize h₁ c hc x h_dxc_le_t c' hc' hneq,
    linarith,
    },
    {intro h,
    intros c hc x h_dist_le_t c' hc' h_c_neq_c',
    have h₁ : d(c,c') ≥ d(C), 
    from dist_neq_codewords_gt_min_distance c c' hc hc' h_c_neq_c',
    have h₂ : d(c,c') ≥ 2 * t + 1, by linarith,
    have h₃ : d(c,c') ≤ d(c,x) + d(x,c'), from hamming.distance_triangle_ineq c c' x,
    calc d(x,c') ≥ d(c,c') - d(c,x)     : by {simp, exact nat.sub_le_left_of_le_add h₃}
    ...          ≥ (2 * t + 1) - d(c,x) : by {simp, exact nat.sub_le_sub_right h₂ d(c,x)}
    ...          ≥ (2 * t + 1) - t      : by {simp, rw hamming.distance_symmetric, 
                                              exact (2 * t + 1).sub_le_sub_left h_dist_le_t}
    ...          = (t + t + 1) - t      : by ring
    ...          = t + 1                : by {rw nat.add_assoc, simp}
    ...          > d(x,c)               : by linarith,
    }
end

open_locale big_operators

def indices (n : ℕ) : finset ℕ := finset.erase (finset.range (n + 1)) 0

@[simp]
lemma indices_card_eq_word_size (n : ℕ) : (indices n).card = n :=
by {rw [indices, finset.card_erase_of_mem], simp, simp}

def bw_to_nonzero_indices : Π {n : ℕ}, BW n → finset ℕ
| 0 nil := finset.empty
| n (O::ᴮtl) := bw_to_nonzero_indices tl
| n (I::ᴮtl) := insert n (bw_to_nonzero_indices tl)

lemma mem_nonzero_indices_le_bw_size (x : BW n) (i : ℕ) : 
  i ∈ (bw_to_nonzero_indices x) → 1 ≤ i → i ≤ n :=
begin
  intros h_mem h_gte_one, 
  induction x with k xhd xtl ih,
    {rw bw_to_nonzero_indices at h_mem, 
    have : i ∉ finset.empty, from finset.not_mem_empty i, 
    contradiction},
  cases xhd,
    {rw bw_to_nonzero_indices at h_mem, specialize ih h_mem, rw ← nat.add_one, linarith},
    {rw bw_to_nonzero_indices at h_mem, 
    rw finset.mem_insert at h_mem, cases h_mem,
      {rw h_mem},
      {specialize ih h_mem, rw ← nat.add_one, linarith},
    }
end

lemma succ_not_mem_nonzero_indices (x : BW n) :
  n.succ ∉ bw_to_nonzero_indices x :=
begin
  by_contradiction h',
  have h₀ : 1 ≤ n.succ, by {rw ← nat.add_one, linarith},
  have h₁ : n.succ ≤ n, from mem_nonzero_indices_le_bw_size x n.succ h' h₀,
  have h₂ : ¬ n.succ ≤ n, from nat.not_succ_le_self n,
  contradiction
end

lemma weight_eq_card_nonzero_indices (x : BW n) : wt(x) = (bw_to_nonzero_indices x).card :=
begin
  induction n with k ih,
    {rw nil_unique x, rw bw_to_nonzero_indices, rw hamming.weight, refl},
  cases x with _ xhd xtl,
  cases xhd,
    {rw [hamming.weight, bw_to_nonzero_indices], apply ih},
    {rw [hamming.weight, bw_to_nonzero_indices], 
    rw finset.card_insert_of_not_mem,
      {rw nat.add_one, simp, apply ih},
      {by_contradiction h, 
      have h₀ : 1 ≤ k.succ, by {rw ← nat.add_one, linarith},
      have h₁ : k.succ ≤ k, from mem_nonzero_indices_le_bw_size xtl k.succ h h₀,
      have h₂ : ¬ k.succ ≤ k, from nat.not_succ_le_self k,
      contradiction,
      }
    }
end

lemma indices_subset_indices_succ (k : ℕ) : indices k ⊆ indices k.succ :=
begin
  repeat {rw indices},
  have h : finset.range (k + 1) ⊆ finset.range (k.succ + 1), by simp,
  exact finset.erase_subset_erase 0 h,
end

lemma nonzero_indices_subset_indices (x : BW n) : (bw_to_nonzero_indices x) ⊆ (indices n) :=
begin
  induction x with k xhd xtl ih,
    {rw [bw_to_nonzero_indices, indices], refl},
  cases xhd,
    {rw bw_to_nonzero_indices, 
    have h : indices k ⊆ indices k.succ, from indices_subset_indices_succ k,
    exact finset.subset.trans ih h},
    {rw [bw_to_nonzero_indices, finset.insert_subset], split,
      {rw indices, simp, exact nat.succ_ne_zero k},
    have h : indices k ⊆ indices k.succ, from indices_subset_indices_succ k,
    exact finset.subset.trans ih h},
end

def nonzero_indices_to_bw : Π (n : ℕ), finset ℕ → BW n
| 0     s := nil
| (n+1) s :=
  if (n + 1) ∈ s then
    (I::ᴮnonzero_indices_to_bw n (s.erase (n + 1)))
  else
    (O::ᴮnonzero_indices_to_bw n s)

lemma erase_last_index_subset {s : finset ℕ} : s ⊆ indices (n + 1) → s.erase (n + 1) ⊆ indices n :=
begin
  unfold indices,
  intros h i hi,
  specialize h (finset.mem_of_mem_erase hi),
  rw finset.mem_erase at *,
  split,
    {exact h.left},
    {rw finset.mem_range,
    refine lt_of_le_of_ne _ hi.left,
    rw ← finset.mem_range_succ_iff,
    exact h.right}
end

lemma last_index_not_mem_subset {s : finset ℕ} : s ⊆ indices (n + 1) → n + 1 ∉ s → s ⊆ indices n :=
begin
  unfold indices,
  intros h h' i hi,
  specialize h hi,
  rw finset.mem_erase at *,
  split,
    {exact h.left},
    {rw finset.mem_range,
    apply lt_of_le_of_ne,
      {rw ← finset.mem_range_succ_iff, exact h.right},
      {intro h, rw h at hi, exact h' hi}
    }
end


lemma bw_to_nonzero_indices_inv_nonzero_indices_to_bw (n : ℕ) (s : finset ℕ) (h : s ⊆ indices n) :
  bw_to_nonzero_indices (nonzero_indices_to_bw n s) = s :=
begin
  revert s,
  induction n with n ih,
    {intros s h, change ∅ = s, symmetry, rwa ← finset.subset_empty},
  intros t h,
  unfold nonzero_indices_to_bw,
  split_ifs with h',
    {specialize ih (t.erase (n + 1)) (erase_last_index_subset h),
    unfold bw_to_nonzero_indices,
    conv_rhs {rw [← finset.insert_erase h', ← ih]}},
    {exact ih t (last_index_not_mem_subset h h')},
end

lemma all_nonzero_indices_eq_powerset_indices :
  finset.image (λ v : BW n, bw_to_nonzero_indices v) finset.univ = (indices n).powerset :=
begin
  simp, ext,
  split,
    {simp, intros x h, rw ← h, exact nonzero_indices_subset_indices x},
    {simp, intro h, use nonzero_indices_to_bw n a, 
    exact bw_to_nonzero_indices_inv_nonzero_indices_to_bw n a h},
end

lemma nonzero_indices_eq_powerset_len (w : ℕ) (h : w ≤ n) : 
  finset.filter (λ s : finset ℕ, s.card = w) 
    (finset.image (λ v : BW n, bw_to_nonzero_indices v) finset.univ)
  = finset.powerset_len w (indices n) :=
begin
  simp,
  rw [finset.powerset_len_eq_filter, all_nonzero_indices_eq_powerset_indices],
end

lemma eq_nonzero_indices_eq_words (a b : BW n) : 
  bw_to_nonzero_indices a = bw_to_nonzero_indices b → a = b :=
begin
  intro h,
  induction a with k ahd atl ih,
    {rw nil_unique b},
  cases b with _ bhd btl,
  cases ahd,
    {cases bhd,
      {simp, exact ih btl h},
      {simp, repeat {rw bw_to_nonzero_indices at h},
      have h : k.succ ∉ bw_to_nonzero_indices atl, from succ_not_mem_nonzero_indices atl,
      have h' : bw_to_nonzero_indices atl ≠ insert k.succ (bw_to_nonzero_indices btl),
      from finset.ne_insert_of_not_mem _ _ h,
      contradiction},
    },
    {cases bhd,
      {simp, repeat {rw bw_to_nonzero_indices at h},
      have h : k.succ ∉ bw_to_nonzero_indices btl, from succ_not_mem_nonzero_indices btl,
      have h' : insert k.succ (bw_to_nonzero_indices atl) ≠ bw_to_nonzero_indices btl,
      from (finset.ne_insert_of_not_mem _ _ h).symm,
      contradiction},
      {simp, repeat {rw [bw_to_nonzero_indices, finset.insert_eq] at h}, 
      have h₁ : k.succ ∉ bw_to_nonzero_indices atl, from succ_not_mem_nonzero_indices atl,
      have h₂ : k.succ ∉ bw_to_nonzero_indices btl, from succ_not_mem_nonzero_indices btl,
      have h₃ : bw_to_nonzero_indices atl ⊆ bw_to_nonzero_indices btl, 
        begin
          rw finset.subset_iff, intros i hi,
          have h' : i ∈ {k.succ} ∪ bw_to_nonzero_indices atl, from finset.mem_union_right _ hi,
          rw h at h', simp at h', cases h',
            {rw ← h' at h₁, contradiction},
            {exact h'},
        end,
      have h₄ : bw_to_nonzero_indices btl ⊆ bw_to_nonzero_indices atl,
        begin
          rw finset.subset_iff, intros i hi,
          have h' : i ∈ {k.succ} ∪ bw_to_nonzero_indices btl, from finset.mem_union_right _ hi,
          rw ← h at h', simp at h', cases h',
            {rw ← h' at h₂, contradiction},
            {exact h'},
        end,
      have h₅ : bw_to_nonzero_indices atl = bw_to_nonzero_indices btl, 
      from finset.subset.antisymm h₃ h₄,
      exact ih btl h₅,
      },
    }
end

lemma filter_size_same_as_size_filter (w : ℕ):
  (finset.filter (λ v : BW n, (bw_to_nonzero_indices v).card = w) finset.univ).card =
  (finset.filter (λ s : finset ℕ, s.card = w) 
    (finset.image (λ v : BW n, bw_to_nonzero_indices v) finset.univ)).card :=
begin
  rw finset.card_congr (λ (v : BW n) h, bw_to_nonzero_indices v),
    {simp},
    {simp, intros a b ha hb hab, exact eq_nonzero_indices_eq_words _ _ hab},
    {simp, intros b hb, use b, split, exact hb, refl},
end

lemma card_nonzero_indices (w : ℕ) (h : w ≤ n) :
  (finset.filter (λ v : BW n, (bw_to_nonzero_indices v).card = w) finset.univ).card = n.choose w :=
begin
  rw [filter_size_same_as_size_filter, nonzero_indices_eq_powerset_len],
  simp, exact h,
end 

lemma num_words_with_weight (w : ℕ) (h : w ≤ n): 
  (finset.filter (λ v : BW n, wt(v) = w) finset.univ).card = n.choose w :=
begin
  conv {to_lhs, congr, congr, funext, rw weight_eq_card_nonzero_indices},
  simp,
  exact card_nonzero_indices w h,
end


def words_at_dist (c : BW n) (r : ℕ) : finset (BW n) :=
finset.filter (λ v, d(c, v) = r) finset.univ

def sphere (c : BW n) (r : ℕ) : finset (BW n) := 
finset.filter (λ v, d(c, v) ≤ r) finset.univ

lemma words_at_dist_mem (c : BW n) (r : ℕ) :
  ∀ (bw : BW n), bw ∈ words_at_dist c r ↔ d(c, bw) = r :=
by {unfold words_at_dist, simp}

lemma sphere_mem (c : BW n) (r : ℕ) : ∀ (bw : BW n), bw ∈ sphere c r ↔ d(c, bw) ≤ r :=
by {unfold sphere, simp}

lemma words_unique (c : BW n) : (finset.filter (eq c) finset.univ).card = 1 :=
by {rw finset.filter_eq finset.univ c, simp}

lemma words_at_ne_dists_disjoint (c : BW n) (r₁ r₂ : ℕ) (h : r₁ ≠ r₂) :
  disjoint (words_at_dist c r₁) (words_at_dist c r₂) :=
begin
  rw finset.disjoint_right,
  by_contradiction h₁, 
  push_neg at h₁,
  cases h₁ with a h_a,
  repeat {rw words_at_dist_mem at h_a},
  have : r₁ = r₂, from hamming.distance_unique c a r₁ r₂ h_a.symm,
  contradiction,
end

lemma words_at_dist_eq_words_with_sum_weight (c : BW n) (r : ℕ) :
  (finset.filter (λ (v : BW n), wt(c + v) = r) finset.univ).card = 
    (finset.filter (λ (v : BW n), wt(v) = r) finset.univ).card :=
begin
  rw finset.card_congr (λ (v : BW n) h, c + v),
    {intros a ha, simp, simp at ha, exact ha},
    {intros a b ha hb, simp},
    {intros b hb, simp, simp at hb,
    use b - c, split,
      {simp, exact hb},
      {simp}
    },
end

lemma words_at_dist_size (c : BW n) (r : ℕ) (h : r ≤ n) : 
  (words_at_dist c r).card = n.choose r :=
begin
  rw words_at_dist,
  conv {to_lhs, congr, congr, funext, rw hamming.distance_eq_weight_of_sum},
  simp,
  rw [words_at_dist_eq_words_with_sum_weight, num_words_with_weight r h],
end

lemma sphere_eq_union_words_at_dist (c : BW n) (r : ℕ) (h : r ≤ n) :
  sphere c r = finset.bUnion (finset.range (r + 1)) (words_at_dist c) :=
begin
  unfold sphere,
  ext,
  split,
    {simp,
    intro h, 
    use d(c,a), 
    split,
      {linarith},
      {rw words_at_dist, simp}},
    {simp,
    intros x hx,
    rw words_at_dist, 
    simp,
    intro h_dist,
    rw h_dist,
    linarith,
    }
end

lemma sphere_size_eq_sum_words_at_dist_size (c : BW n) (r : ℕ) (h : r ≤ n) :
  (sphere c r).card = ∑ i in (finset.range (r + 1)), (words_at_dist c i).card :=
begin
  rw sphere_eq_union_words_at_dist,
  rw finset.card_bUnion,
    {intros x hx y hy h_ne, 
    exact words_at_ne_dists_disjoint c x y h_ne},
    {exact h},
end

lemma sphere_size (c : BW n) (r : ℕ) (h : r ≤ n) : 
  (sphere c r).card = ∑ i in (finset.range (r + 1)), n.choose i :=
begin
  rw sphere_size_eq_sum_words_at_dist_size c r h,
  apply finset.sum_congr,
    {refl},
  intros h hx,
  rw words_at_dist_size,
  simp at hx,
  linarith,
end

lemma t_error_correcting_spheres_disjoint (t : ℕ) 
  (t_error_correcting : ∀ (c ∈ C) (x : BW n), (d(x,c) ≤ t → (∀ (c' ∈ C), c ≠ c' → d(x,c) < d(x,c')))) :
  ∀ (c₁ c₂ ∈ C), c₁ ≠ c₂ → disjoint (sphere c₁ t) (sphere c₂ t) :=
begin
  rw t_error_correcting_iff_min_distance_gte at t_error_correcting,
  intros c₁ c₂ hc₁ hc₂ hne,
  rw finset.disjoint_left,
  repeat {rw sphere}, simp,
  intros x hc₁x,
  by_contradiction hc₂x, push_neg at hc₂x,
  have h₁ : d(c₁,c₂) ≤ d(c₁,x) + d(x,c₂), from hamming.distance_triangle_ineq c₁ c₂ x,
  have h₂ : d(c₁,c₂) ≤ 2 * t,
  from calc d(c₁,c₂) ≤ t + d(x,c₂) : le_add_of_le_add_right h₁ hc₁x
  ...                ≤ t + t       : by {simp, rw hamming.distance_symmetric, exact hc₂x}
  ...                = 2 * t       : by ring,
  have h₃ : d(C) ≤ d(c₁,c₂), from dist_neq_codewords_gt_min_distance c₁ c₂ hc₁ hc₂ hne,
  linarith,
end

theorem hamming_bound (t : ℕ) (ht : t ≤ n)
  (t_error_correcting : ∀ (c ∈ C) (x : BW n), (d(x,c) ≤ t → (∀ (c' ∈ C), c ≠ c' → d(x,c) < d(x,c')))) :
  C.cws.card ≤ 2 ^ n / ∑ i in (finset.range (t + 1)), n.choose i :=
begin
  -- have : (finset.bUnion C.cws (λ c, sphere c t)).card = ∑ (u : BW n) in C.cws, (sphere u t).card,
  -- begin
  --   rw finset.card_bUnion,
  --   intros x hx y hy hne,
  --   exact (t_error_correcting_spheres_disjoint t t_error_correcting) x y hx hy hne,
  -- end,
  -- have : ∑ (u : BW n) in C.cws, (sphere u t).card = 
  --        ∑ (u : BW n) in C.cws, ∑ i in (finset.range (t + 1)), n.choose i,
  -- begin
  --   rw finset.sum_congr,
  --     {refl},
  --   intros x hx,
  --   exact sphere_size x t ht,
  -- end,
  -- have : ∑ (u : BW n) in C.cws, ∑ i in (finset.range (t + 1)), n.choose i =
  --        C.cws.card * ∑ i in (finset.range (t + 1)), n.choose i,
  -- by simp,
  sorry
end

end binary_linear_code

-- def H74C : finset (BW 7) := {
--   val := {
--     ᴮ[O,O,O,O,O,O,O],
--     ᴮ[I,I,O,I,O,O,I],
--     ᴮ[O,I,O,I,O,I,O],
--     ᴮ[I,O,O,O,O,I,I],
--     ᴮ[I,O,O,I,I,O,O],
--     ᴮ[O,I,O,O,I,O,I],
--     ᴮ[I,I,O,O,I,I,O],
--     ᴮ[O,O,O,I,I,I,I],
--     ᴮ[I,I,I,O,O,O,O],
--     ᴮ[O,O,I,I,O,O,I],
--     ᴮ[I,O,I,I,O,I,O],
--     ᴮ[O,I,I,O,O,I,I],
--     ᴮ[O,I,I,I,I,O,O],
--     ᴮ[I,O,I,O,I,O,I],
--     ᴮ[O,O,I,O,I,I,O],
--     ᴮ[I,I,I,I,I,I,I]
--   },
--   nodup := by simp,
-- }

-- def hamming74Code : binary_linear_code 7 4 3 :=
-- {
--   cws := H74C,
--   card_gte := by {have : H74C.card = 16, from rfl, linarith},
--   is_subspace := {
--     carrier := H74C,
--     zero_mem' := by {simp, left, refl},
--     add_mem' := begin
--       rintros a b
--         (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha)
--         (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb),
--         all_goals {
--           try {rw list.eq_of_mem_singleton ha}, 
--           try {rw list.eq_of_mem_singleton hb}, 
--           repeat {{left, refl} <|> right <|> refl},
--         },
--         all_goals {simp, refl},
--     end,
--     smul_mem' := begin
--       intros c x x_mem,
--       cases c,
--         {conv {congr, apply_congr zero_smul}, simp, left, refl},
--         {conv {congr, apply_congr one_smul}, exact x_mem}
--     end,
--   },
-- }

-- #eval d(hamming74Code)
-- #eval d(ᴮ[I,I,O,I,O,O,I],ᴮ[O,I,O,I,O,I,O])
-- def c1 := binary_linear_code.change_t_disagreements 2 ᴮ[I,I,O,I,O,O,I] ᴮ[O,I,O,I,O,I,O]
-- #eval c1
-- #eval d(ᴮ[I,I,O,I,O,O,I],c1)
-- #eval d(ᴮ[O,I,O,I,O,I,O],c1)