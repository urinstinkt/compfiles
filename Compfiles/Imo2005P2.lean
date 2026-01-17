/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2005, Problem 2

Let $a_1, a_2, \dots$ be a sequence of integers with infinitely many positive and negative terms.
Suppose that for every positive integer $n$ the numbers $a_1, a_2, \dots, a_n$ leave $n$ different remainders upon division by $n$.
Prove that every integer occurs exactly once in the sequence.
-/

namespace Imo2005P2

/-def prefix_list (a : ℕ → ℤ) (n : ℕ) : List ℤ :=
  match n with
  | 0 => []
  | n+1 => (prefix_list a n) ++ [a n]

def prefix_finset (a : ℕ → ℤ) (n : ℕ) : Finset ℤ :=
  match n with
  | 0 => ∅
  | n+1 => (prefix_finset a n) ∪ {a n}-/

snip begin

def prefix_max (a : ℕ → ℤ) (n : ℕ) (npos : 0 < n) : ℤ :=
  Finset.max' ((Finset.range n).image (fun i => a i)) (by {
    simp only [Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq]
    exact Nat.ne_zero_of_lt npos
  })

def prefix_min (a : ℕ → ℤ) (n : ℕ) (npos : 0 < n) : ℤ :=
  Finset.min' ((Finset.range n).image (fun i => a i)) (by {
    simp only [Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq]
    exact Nat.ne_zero_of_lt npos
  })

theorem mod_nonzero (a : ℕ → ℤ) (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n > 0, ∀ d > n, ¬ a n % d = 0 := by
  intro n npos d dgt
  contrapose! rem
  use d, (by grind)
  nth_rw 3 [<-Finset.card_range d]
  rw [ne_eq, Finset.card_image_iff]
  rw [Set.InjOn]
  simp only [Finset.coe_range, Set.mem_Iio, not_forall, exists_prop]
  use 0, ?_, n, ?_, ?_
  · exact Nat.ne_of_lt npos
  · grind
  · exact dgt
  · rw [rem, a0]
    simp

theorem nonzero (a : ℕ → ℤ) (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n > 0, ¬ a n = 0 := by
  intro n npos
  have : _ := mod_nonzero _ rem a0 n npos (n+1) (by simp)
  contrapose! this
  rw [this]
  simp

theorem abs_bound (a : ℕ → ℤ) (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n, |a n| ≤ n := by
  intro n
  by_cases nz : n = 0
  · subst nz
    rw [a0]
    simp
  by_contra! c
  have : ¬ a n % (a n).natAbs = 0 := by
    apply mod_nonzero a rem a0 n
    · exact Nat.zero_lt_of_ne_zero nz
    · grind
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Int.emod_abs, EuclideanDomain.mod_self,
    not_true_eq_false] at this



/-def next_smallest_nonneg (a : ℕ → ℤ) (n : ℕ) := Nat.find (p:=fun x => x.cast ∉ {a i | i < n}) (by {
  use ((Finset.max ((Finset.range n).image (fun i => a i + 1))).getD 0).natAbs
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Set.mem_setOf_eq, not_exists, not_and]
  intro i iltn
  apply ne_of_lt
  rw [lt_abs]
  apply Or.inl
  unfold Option.getD
  split
  · expose_names
    refine Int.lt_of_add_one_le ?_
    rw [<-WithBot.coe_le_coe, WithBot.some, <-heq]
    apply Finset.le_max
    simp only [Finset.mem_image, Finset.mem_range, add_left_inj]
    use i
  · expose_names
    rw [WithBot.none_eq_bot, Finset.max_eq_bot] at heq
    simp only [Finset.image_eq_empty, Finset.range_eq_empty_iff] at heq
    grind
})

def next_largest_nonpos (a : ℕ → ℤ) (n : ℕ) := Nat.find (p:=fun x => -x.cast ∉ {a i | i < n}) (by {
  use ((Finset.max ((Finset.range n).image (fun i => a i + 1))).getD 0).natAbs
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Set.mem_setOf_eq, not_exists, not_and]
  intro i iltn
  apply ne_of_lt
  rw [lt_abs]
  apply Or.inl
  unfold Option.getD
  split
  · expose_names
    refine Int.lt_of_add_one_le ?_
    rw [<-WithBot.coe_le_coe, WithBot.some, <-heq]
    apply Finset.le_max
    simp only [Finset.mem_image, Finset.mem_range, add_left_inj]
    use i
  · expose_names
    rw [WithBot.none_eq_bot, Finset.max_eq_bot] at heq
    simp only [Finset.image_eq_empty, Finset.range_eq_empty_iff] at heq
    grind
})-/

def consecutive {S : Type} [SetLike S ℤ] (s : S) : Prop := ∀ (a b c : ℤ), a < b → b < c → a ∈ s → c ∈ s → b ∈ s

theorem consecutive' {S : Type} [SetLike S ℤ] {s : S} (h : consecutive s) : ∀ (a b c : ℤ), a ≤ b → b ≤ c → a ∈ s → c ∈ s → b ∈ s := by
  unfold consecutive at h
  grind only

theorem consecutive_insert_max' (s : Finset ℤ) (hne : s.Nonempty) (hc : consecutive s) : consecutive (insert (s.max' hne + 1) s) := by
  intro a b c h1 h2 u1 u2
  by_cases m : c < s.max' hne + 1
  · suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc a b c h1 h2 <;> grind only [= Finset.mem_insert]
  · have : c = s.max' hne + 1 := by
      simp at m
      simp at u2
      apply u2.by_cases (by simp)
      intro h
      have : s.max' hne < c := by exact (Finset.max'_lt_iff s hne).mpr m
      rw [Finset.max'_lt_iff s hne (x:=c)] at this
      grind only [this _ h]
    subst this
    by_cases m' : b = s.max' hne
    · subst m'
      simp only [Finset.mem_insert, left_eq_add, one_ne_zero, false_or]
      exact Finset.max'_mem s hne
    have : b < s.max' hne := by omega
    suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc a b (s.max' hne) h1 this
    · grind
    · exact Finset.max'_mem s hne

/-theorem Finset.neg_min' (s : Finset ℤ) (hne : s.Nonempty) : - s.min' hne = (s.image (-·)).max' (by simp [hne]) := by
  sorry

theorem Finset.neg_min (s : Finset ℤ) : - s.min = (s.image (-·)).max := by
  sorry

theorem consecutive_insert_min' (s : Finset ℤ) (hne : s.Nonempty) (hc : consecutive s) : consecutive (insert (s.min' hne - 1) s) := by
  rw [<-neg_neg (s.min' hne), Finset.neg_min']
  rw [show ∀ x, -x - 1 = -(x + 1) by omega]
  have : s = (s.image (-·)).image (-·) := by
    ext
    simp
  nth_rw 2 [this]
  rw [Finset.image_insert]
-/

theorem consecutive_insert_min' (s : Finset ℤ) (hne : s.Nonempty) (hc : consecutive s) : consecutive (insert (s.min' hne - 1) s) := by
  intro a b c h1 h2 u1 u2
  by_cases m : s.min' hne - 1 < a
  · suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc a b c h1 h2 <;> grind only [= Finset.mem_insert]
  · have : a = s.min' hne - 1 := by
      simp at m
      simp at u1
      apply u1.by_cases (by simp)
      intro h
      have : a < s.min' hne := by exact (Finset.lt_min'_iff s hne).mpr m
      rw [Finset.lt_min'_iff s hne (x:=a)] at this
      grind only [this _ h]
    subst this
    by_cases m' : b = s.min' hne
    · subst m'
      refine Finset.mem_insert_of_mem ?_
      exact Finset.min'_mem s hne
    have : s.min' hne < b := by omega
    suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc (s.min' hne) b c this h2
    · exact Finset.min'_mem s hne
    · grind

--theorem consecutive_decomp (s : Finset ℤ) (hne : s.Nonempty) (hc : consecutive s) : consecutive (insert (s.min' hne - 1) s) := by

theorem max'_sub_min'_of_consecutive (s : Finset ℤ) (ne : s.Nonempty) (con : consecutive s)
: s.max' ne - s.min' ne = s.card - 1 := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases single : s.card ≤ 1
    · obtain ⟨x, xh⟩ : ∃ x, s = {x} := by
        refine Finset.card_eq_one.mp ?_
        grind only [= Finset.nonempty_def, usr Finset.card_ne_zero_of_mem]
      subst s
      simp
    · let t := s \ {s.max' ne}
      have tne : t.Nonempty := by
        contrapose! single
        subst t
        simp only [Finset.sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff] at single
        grind
      have tcons : consecutive t := by
        intro a b c ab bc ah ch
        have ah : a ∈ s := by simp_all only [Finset.mem_sdiff, t]
        have ch : c ∈ s := by simp_all only [Finset.mem_sdiff, t]
        unfold t
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        and_intros
        · apply con a b c ab bc ah ch
        · by_contra!
          subst b
          rw [Finset.max'_lt_iff] at bc
          let := bc c
          simp [ch] at this
      have : t.max' tne + 1 = s.max' ne := by
        suffices s.max' ne - 1 ∈ t by
          rw [add_eq_of_eq_sub]
          rw [Finset.max'_eq_iff]
          simp only [this, true_and]
          intro x xh
          unfold t at xh
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at xh
          rw [Order.le_sub_one_iff, lt_iff_le_and_ne]
          simp [xh.right]
          apply Finset.le_max' _ _ xh.left
        unfold t
        simp only [Finset.mem_sdiff, Finset.mem_singleton, sub_eq_self, one_ne_zero,
          not_false_eq_true, and_true]
        apply consecutive' con (s.min' ne) _ (s.max' ne)
        · simp
          apply Finset.min'_lt_max'_of_card
          exact Nat.lt_of_not_le single
        · simp
        · exact Finset.min'_mem s ne
        · exact Finset.max'_mem s ne
      rw [<-this]
      have seq : s = t ∪ {t.max' tne + 1} := by
        unfold t
        rw [this]
        refine Eq.symm (Finset.sdiff_union_of_subset ?_)
        simp [Finset.max'_mem s _]
      have : t.min' tne = s.min' ne := by
        rw [eq_comm, Finset.min'_eq_iff, seq]
        and_intros
        · apply Finset.mem_union_left
          exact Finset.min'_mem t tne
        · intro x xu
          simp only [Finset.union_singleton, Finset.mem_insert] at xu
          apply xu.by_cases
          · intro _
            subst x
            apply le_trans (Finset.min'_le_max' _ _)
            simp
          · apply Finset.min'_le
      rw [<-this]
      have : s.card = t.card + 1 := by
        rw [seq, Finset.union_singleton, Finset.card_insert_of_notMem]
        by_contra! c
        let := Finset.le_max' t _ c
        simp at this
      rw [this]
      let ih := ih t ?_ tne ?_
      · omega
      · rw [seq]
        constructor
        · simp
        · refine Finset.not_subset.mpr ?_
          use t.max' tne +1
          simp only [Finset.union_singleton, Finset.mem_insert, true_or, true_and]
          by_contra! c
          let := Finset.le_max' t _ c
          simp at this
      · exact tcons


theorem an_inductive' (a : ℕ → ℤ) --(pos_inf : Set.Infinite {i | 0 < a i}) (neg_inf : Set.Infinite {i | a i < 0})
  (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n, consecutive ((Finset.range n).image (fun i => a i)) ∧ ∀ npos: n > 0, (a n = prefix_max a n npos + 1 ∨ a n = prefix_min a n npos - 1) := by
  intro n

  induction n with
  | zero =>
    unfold consecutive
    simp
  | succ n ih =>
    rw [show ∀ (a b : Prop), a ∧ b ↔ a ∧ (a → b) by grind only]
    and_intros
    · have : Finset.image (fun i ↦ a i) (Finset.range (n + 1)) = insert (a n) (Finset.image (fun i ↦ a i) (Finset.range n)) := by
        rw [Finset.insert_eq]
        ext x
        simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff, Finset.singleton_union,
          Finset.mem_insert]
        grind
      rw [this]
      by_cases npos : 0 < n
      · apply (ih.right npos).by_cases
        · intro h
          rw [h]
          apply consecutive_insert_max'
          apply ih.left
        · intro h
          rw [h]
          apply consecutive_insert_min'
          apply ih.left
      · simp only [not_lt, nonpos_iff_eq_zero] at npos
        subst npos
        intro x y z
        grind
    · intro con npos'
      --have : consecutive (Finset.image (fun i ↦ a i % (n+1)) (Finset.range (n + 1))) := by
      --  sorry
      have notmod : ∀ i ≤ n, ¬ a i ≡ a (n+1) [ZMOD n+2] := by
        intro i ilen
        contrapose! rem
        use n+2, (by simp)
        nth_rw 3 [<-Finset.card_range (n+2)]
        rw [ne_eq, Finset.card_image_iff]
        rw [Set.InjOn]
        simp
        use i, (by grind), n+1, (by simp)
        and_intros
        · exact Int.ModEq.eq rem
        · grind only
      have notmod' : ∀ i ≤ n, ¬ a i = (a (n+1) : ZMod (n+2)) := by
        intro i ilen
        contrapose! rem
        use n+2, (by simp)
        nth_rw 3 [<-Finset.card_range (n+2)]
        rw [ne_eq, Finset.card_image_iff]
        rw [Set.InjOn]
        simp
        use i, (by grind), n+1, (by simp)
        and_intros
        · rw [ZMod.intCast_eq_intCast_iff] at rem
          exact Int.ModEq.eq rem
        · grind only
      have notmem : ¬ a (n+1) ∈ (Finset.image (fun i ↦ a i) (Finset.range (n + 1))) := by
        simp
        intro i ih1 ih2
        let := notmod i ih1
        rw [ih2] at this
        contradiction
      let modset := Finset.image (fun i ↦ a i % ↑(n+2)) (Finset.range (n+2))
      have modset_Ico : modset = Finset.Ico (α:=ℤ) 0 (n+2) := by
        unfold modset
        rw [<-Finset.eq_iff_card_le_of_subset]
        · rw [rem]
          repeat simp
        · refine Finset.image_subset_iff.mpr ?_
          intro i _
          rw [Finset.mem_Ico]
          and_intros
          · apply Int.emod_nonneg
            omega
          · apply Int.emod_lt_of_pos
            omega
      --let zmodset := @Finset.univ (ZMod (n+2)) inferInstance
      --have equiv1 : _ := Finset.equivOfCardEq (s:= modset) (t:=zmodset) (by rw [rem (n+2) (by simp), Finset.card_univ, ZMod.card])
      have hmodmax : prefix_max a (n + 1) npos' + 1 = (a (n + 1) : ZMod (n+2)) := by
        have : (a (n+1) - 1) % (n+2) ∈ modset := by
          rw [modset_Ico, Finset.mem_Ico]
          and_intros
          · apply Int.emod_nonneg
            omega
          · apply Int.emod_lt_of_pos
            omega
        unfold modset at this
        simp only [Nat.cast_add, Nat.cast_ofNat, Finset.mem_image, Finset.mem_range] at this
        let ⟨i, h1, h2⟩ := this
        rw [<-Int.ModEq] at h2
        rw [show @Nat.cast ℤ _ n + 2 = (n+2).cast by simp] at h2
        rw [<-ZMod.intCast_eq_intCast_iff] at h2
        have h1 : i < n+1 := by
          by_contra
          have : i = n+1 := by omega
          subst i
          rw [<-sub_eq_zero] at h2
          simp only [Int.cast_sub, Int.cast_one, sub_sub_cancel] at h2
          rw [ZMod.one_eq_zero_iff] at h2
          grind only
        have : a i + 1 = (a (n + 1) : ZMod (n+2)) := by
          rw [h2]
          simp
        rw [<-this]
        simp only [add_left_inj]
        unfold prefix_max
        let := Finset.max'_mem (Finset.image (fun i ↦ a i) (Finset.range (n + 1))) (by simp)
        simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
        let ⟨j, jb, jh⟩ := this
        rw [<-jh]
        congr
        by_contra c
        let := consecutive' con (a i) (a i + 1) (a j) (by simp) ?_ ?_ ?_
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
          let ⟨k, kh1, kh2⟩ := this
          contrapose! notmod'
          use k, kh1
          rw [kh2, Int.cast_add, h2]
          simp
        · rw [jh]
          rw [Order.add_one_le_iff]
          apply Finset.lt_max'_of_mem_erase_max'
          simp only [Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_range,
            Order.lt_add_one_iff]
          rw [<-jh]
          and_intros
          · have : Function.Injective a := by
              sorry
            rw [Eq.comm]
            exact Ne.intro fun x ↦ c (this x)
          · use i
            simp only [and_true]
            exact Nat.le_of_lt_succ h1
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
          use i
          simp [Nat.le_of_lt_succ h1]
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
          use j
      by_cases pos : a (n+1) > 0
      · apply Or.inl
        have h_gt : a (n+1) > prefix_max a (n + 1) npos' := by
          rw [gt_iff_lt]
          unfold prefix_max
          rw [Finset.max'_lt_iff]
          simp
          by_contra! c
          let ⟨i, ih1, ih2⟩ := c
          let := consecutive' con (a 0) (a (n+1)) (a i) (by grind) ih2 (by grind) (by grind)
          contradiction

        sorry
      · apply Or.inr
        -- wlog??
        sorry

/-
      have modset_add_one : ∀ i≤n, ¬ a i = prefix_max a (n + 1) npos' → (a i + 1)%(n+2) ∈ modset := by
        intro i ib h
        obtain ⟨j, jb, jh⟩ : ∃ j ≤ n+1, a j = a i + 1 := by
          let := consecutive' con (a i) (a i + 1) (prefix_max a (n + 1) npos') (by simp) ?_ ?_ ?_
          · simp at this
            let ⟨j, jh1, jh2⟩ := this
            use j, (Nat.le_add_right_of_le jh1)
          · rw [Int.add_one_le_iff, lt_iff_le_and_ne]
            and_intros
            · apply Finset.le_max'
              rw [Finset.mem_image]
              use i
              simp [ib]
            · exact h
          · simp
            use i
          · unfold prefix_max
            apply Finset.max'_mem
        rw [<-jh]
        rw [Finset.mem_image]
        use j
        simp [Nat.lt_succ_of_le jb]

      have notmod_max_add_one : ∀ i ≤ n, ¬ a i ≡ (prefix_max a (n + 1) npos' + 1) [ZMOD n+2] := by
        obtain ⟨j, jb, jh⟩ : ∃ j ≤ n, prefix_max a (n+1) npos' = a j := by
          unfold prefix_max
          let := Finset.max'_mem _ (prefix_max._proof_1 a _ npos')
          simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
          simp_rw [eq_comm]
          exact this
        simp_rw [jh]
        contrapose! con
        let ⟨i, ib, ih⟩ := con
        unfold consecutive
        simp
        by_cases c : i=j
        · subst c
          simp at ih
          let := Int.eq_one_of_dvd_one (by grind) ih
          omega
        --by_cases c' : i=j-1
        --· subst c'
        · use a j - 1, i, ?_, j
          · and_intros
            · simp
            · exact ib
            · exact jb
            · contrapose! ih
          · sorry


      have m_max : (prefix_max a (n + 1) npos' + 1) ≡ a (n+1) [ZMOD n+2] := by

        sorry
      sorry



  /-suffices (∀ npos: n > 0, a n = prefix_max a n npos + 1 ∨ a n = prefix_min a n npos - 1)
        --∧ (Finset.range n).image (fun i => a i % n) = (Finset.range n).image (·.cast)
        ∧ ∀ i ≤ n, a i % (n+1) = i
      by exact this.left

  induction n with
  | zero =>
    simp [a0]
  | succ n ih =>
    and_intros
    · intro nb
      sorry
    · intro i ib
      by_cases c : 0 ≤ a i
      · rw [Int.emod_eq_of_lt c (by sorry)]
        let ih := ih.right i
        by_cases ilen : i ≤ n
        · let ih := ih ilen
          by_cases h : a i = n
          · rw [h] at ih
            simp only [Nat.cast_nonneg, Int.emod_self_add_one, Nat.cast_inj] at ih
            subst ih
            exact h
          · rw [Int.emod_eq_of_lt c] at ih
            · exact ih
            · simp only [Order.lt_add_one_iff]
              trans |a i|
              · exact le_abs_self _
              · let := abs_bound a pos_inf neg_inf rem a0 i
                grind
        · have : i = n+1 := by grind
          subst this
          sorry
      · sorry
    --have mod_1 : a n % n = prefix_max a (n+1) npos + 1 := by
    --  sorry-/

    /-· refine Finset.image_congr ?_
      intro i ir
      simp only [Nat.cast_add, Nat.cast_one]
      by_cases c : 0 ≤ a i
      · rw [Int.emod_eq_of_lt c]-/
-/

/-theorem an_inductive (a : ℕ → ℤ) (pos_inf : Set.Infinite {i | 0 < a i}) (neg_inf : Set.Infinite {i | a i < 0})
  (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n, a n = next_smallest_nonneg a n ∨ a n = next_largest_nonpos a n  := by
  sorry-/

snip end

problem imo2005_p2 (a : ℕ → ℤ) (pos_inf : Set.Infinite {a i | (i) (pos: 0 < a i)}) (neg_inf : Set.Infinite {a i | (i) (neg: a i < 0)})
  (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n)
: ∀ z : ℤ, ∃! i, a i = z := by
  wlog a0 : a 0 = 0
  · let a' (i) := a i - a 0
    have : _ := this a' ?_ ?_ ?_ ?_
    · intro z
      unfold a' at this
      let := this (z - a 0)
      simp only [sub_left_inj] at this
      exact this
    · unfold a'
      apply Set.infinite_of_not_bddAbove
      have : Set.Infinite ((·.toNat) '' {a i | (i) (pos: 0 < a i)}) := by
        refine Set.Infinite.image ?_ pos_inf
        intro x1 h1 x2 h2 e
        grind
      let := Set.Infinite.not_bddAbove this
      rw [not_bddAbove_iff] at this ⊢
      intro b
      let ⟨y, yh⟩ := this (b.natAbs + (a 0).natAbs)
      use y - a 0
      simp only [exists_prop, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and,
        Int.sub_pos, sub_left_inj] at yh ⊢
      let ⟨⟨i, h1, h2⟩, h3⟩ := yh
      and_intros
      · use i
        and_intros
        · grind only
        · grind only
      · grind only
    · unfold a'
      apply Set.infinite_of_not_bddBelow
      have : Set.Infinite ((fun x => (-x).toNat) '' {a i | (i) (neg: a i < 0)}) := by
        refine Set.Infinite.image ?_ neg_inf
        intro x1 h1 x2 h2 e
        grind
      let := Set.Infinite.not_bddAbove this
      rw [not_bddAbove_iff] at this
      rw [not_bddBelow_iff] at ⊢
      intro b
      let ⟨y, yh⟩ := this (b.natAbs + (a 0).natAbs)
      use -y - a 0
      simp only [exists_prop, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and, sub_neg,
        sub_left_inj] at yh ⊢
      let ⟨⟨i, h1, h2⟩, h3⟩ := yh
      and_intros
      · use i
        and_intros
        · grind only
        · grind only
      · grind only
    · intro n npos
      nth_rw 3 [<-rem n npos]
      apply Finset.card_bij (fun x h => (x + a 0)%n)
      · simp
        intro x xltn
        use x
        and_intros
        · exact xltn
        · unfold a'
          simp
      · unfold a'
        simp only [Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Int.emod_add_emod, sub_add_cancel]
        intro x1 _ x2 _ e
        rw [Int.sub_emod, Int.sub_emod]
        rw [e]
        simp
      · simp only [Finset.mem_image, Finset.mem_range, exists_prop, exists_exists_and_eq_and,
          Int.emod_add_emod, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro x xltn
        use x
        and_intros
        · exact xltn
        · unfold a'
          simp
    · unfold a'
      simp
  sorry


end Imo2005P2
