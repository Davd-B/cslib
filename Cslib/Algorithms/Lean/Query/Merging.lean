/-
Copyright (c) 2026 Davd-B. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davd-B
-/
module

public import Cslib.Algorithms.Lean.Query.Maximum
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas

/-! # Merging two sorted lists with comparison queries

Merging two sorted lists with `n` elements in total needs `n - 1` comparisons in the worst case,
when the two lists have balanced lengths.

* `IsMerger merge` is the specification of a comparison-based merging program, modeled on
  `IsSort`.
* `merge_isMerger` proves that the standard `merge` (the one used by `mergeSort`) is correct, and
  `merge_countQueries_le_sub_one` proves that it makes at most `n - 1` queries for every oracle.
* `IsMerger.sub_one_le_countQueries` proves that *every* correct merging program makes at least
  `n - 1` queries on the interleaved input `interleaved e n`, whose two lists have lengths
  `⌈n / 2⌉` and `⌊n / 2⌋`. `IsMerger.lowerBound` restates this as a `Query.LowerBound`.

The lower bound is the classical adversary argument: if the two lists interleave perfectly, then
every two elements that are adjacent in the merged output come from different lists. Swapping
them in the order keeps both input lists sorted but changes the correct output, so a correct
program must ask the one comparison that tells the two orders apart.

The bound is specific to balanced lengths: merging a list of length `1` into one of length `n`
only needs `⌈log₂ (n + 1)⌉` comparisons (binary insertion).

## References

* [D. E. Knuth, *The Art of Computer Programming, Volume 3*][Knuth1998], Section 5.3.2.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Specification -/

/-- `merge` is a correct comparison-based merging program: it always produces a permutation of
the concatenation of its inputs, and when the oracle implements a total preorder `r` and both
inputs are sorted with respect to `r`, the output is sorted with respect to `r`. -/
structure IsMerger (merge : List α → List α → FreeM (LEQuery α) (List α)) : Prop where
  /-- The output is a permutation of the concatenated inputs, for any oracle. -/
  perm : ∀ (xs ys : List α) (oracle : {ι : Type} → LEQuery α ι → ι),
    ((merge xs ys).eval oracle).Perm (xs ++ ys)
  /-- The output is sorted, when the oracle implements a total preorder and the inputs are
  sorted. -/
  sorted : ∀ (xs ys : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (_ : ∀ a b, oracle (.le a b) = decide (r a b)),
    xs.Pairwise r → ys.Pairwise r → ((merge xs ys).eval oracle).Pairwise r

/-! ## The standard merge -/

theorem merge_isMerger : IsMerger (merge (α := α)) where
  perm xs ys oracle := by
    rw [eval_merge]
    exact List.merge_perm_append _
  sorted xs ys oracle r _ _ _ horacle hxs hys := by
    rw [eval_merge]
    refine (List.pairwise_merge ?_ ?_ xs ys (hxs.imp ?_) (hys.imp ?_)).imp ?_
    · intro a b c hab hbc
      simp only [horacle, decide_eq_true_eq] at hab hbc ⊢
      exact _root_.trans hab hbc
    · intro a b
      simp only [horacle, Bool.or_eq_true, decide_eq_true_eq]
      exact Std.Total.total a b
    · intro a b h
      simpa [horacle] using h
    · intro a b h
      simpa [horacle] using h
    · intro a b h
      simpa [horacle] using h

/-- The standard merge makes at most `n - 1` queries on inputs with `n` elements in total. -/
theorem merge_countQueries_le_sub_one (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs ys : List α) :
    (merge xs ys).countQueries oracle ≤ xs.length + ys.length - 1 := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    induction ys with
    | nil => simp
    | cons y ys ihy =>
      rw [countQueries_merge_cons_cons]
      split
      · have := ih (y :: ys)
        simp only [List.length_cons] at this ⊢
        omega
      · simp only [List.length_cons] at ihy ⊢
        omega

/-- The standard merge uses at most `n - 1` queries on inputs with `n` elements in total. -/
theorem merge_upperBound :
    UpperBound (fun p : List α × List α => merge p.1 p.2) (fun p => p.1.length + p.2.length)
      (· - 1) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.sub_le_sub_right h 1) fun oracle p =>
    merge_countQueries_le_sub_one oracle p.1 p.2

/-! ## The adversary argument -/

private theorem pairwise_rel_or_rel {R : α → α → Prop} {a b : α} :
    ∀ {l : List α}, l.Pairwise R → a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, ha, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact Or.inl (h.1 b hb')
    · exact Or.inr (h.1 a ha')
    · exact pairwise_rel_or_rel h.2 ha' hb' hab

/-- Let `r` and `r'` be two total preorders under which both inputs are sorted, and let `a ≠ b`
be two input elements whose relative order is not the same under `r` and `r'`. Then any correct
merging program, run against the oracle for `r`, asks a comparison on which the oracles for `r`
and `r'` disagree. -/
theorem IsMerger.exists_comparison_ne
    {merge : List α → List α → FreeM (LEQuery α) (List α)} (hmerge : IsMerger merge)
    (xs ys : List α) (oracle oracle' : {ι : Type} → LEQuery α ι → ι)
    (r r' : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    [DecidableRel r'] [Std.Total r'] [IsTrans α r']
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (horacle' : ∀ a b, oracle' (.le a b) = decide (r' a b))
    (hxs : xs.Pairwise r) (hys : ys.Pairwise r) (hxs' : xs.Pairwise r') (hys' : ys.Pairwise r')
    {a b : α} (ha : a ∈ xs ++ ys) (hb : b ∈ xs ++ ys) (hab : a ≠ b)
    (hr : ¬ (r a b ∧ r' a b)) (hr' : ¬ (r b a ∧ r' b a)) :
    ∃ q ∈ comparisons oracle (merge xs ys), oracle (.le q.1 q.2) ≠ oracle' (.le q.1 q.2) := by
  by_contra! hagree
  have heval : (merge xs ys).eval oracle = (merge xs ys).eval oracle' :=
    eval_eq_of_comparisons _ _ _ hagree
  have hsorted : ((merge xs ys).eval oracle).Pairwise fun c d => r c d ∧ r' c d := by
    refine (hmerge.sorted xs ys oracle r horacle hxs hys).and ?_
    rw [heval]
    exact hmerge.sorted xs ys oracle' r' horacle' hxs' hys'
  have hperm := hmerge.perm xs ys oracle
  rcases pairwise_rel_or_rel hsorted (hperm.mem_iff.mpr ha) (hperm.mem_iff.mpr hb) hab with
    h | h
  · exact hr h
  · exact hr' h

/-! ## The interleaved input -/

/-- The input on which merging needs the most comparisons: the elements `e 0, …, e (n - 1)`,
split into those with an even index and those with an odd index. -/
def interleaved (e : ℕ ↪ α) (n : ℕ) : List α × List α :=
  ((List.range ((n + 1) / 2)).map fun i => e (2 * i),
    (List.range (n / 2)).map fun i => e (2 * i + 1))

@[simp] theorem length_interleaved_fst (e : ℕ ↪ α) (n : ℕ) :
    (interleaved e n).1.length = (n + 1) / 2 := by
  simp [interleaved]

@[simp] theorem length_interleaved_snd (e : ℕ ↪ α) (n : ℕ) :
    (interleaved e n).2.length = n / 2 := by
  simp [interleaved]

theorem mem_interleaved (e : ℕ ↪ α) {n j : ℕ} (hj : j < n) :
    e j ∈ (interleaved e n).1 ++ (interleaved e n).2 := by
  simp only [interleaved, List.mem_append, List.mem_map, List.mem_range]
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · exact Or.inl ⟨i, by omega, rfl⟩
  · exact Or.inr ⟨i, by omega, rfl⟩

/-- Compare elements by a natural-number key. -/
private def keyLE (f : α → ℕ) (a b : α) : Prop := f a ≤ f b

private instance (f : α → ℕ) : DecidableRel (keyLE f) := fun a b =>
  inferInstanceAs (Decidable (f a ≤ f b))

private instance (f : α → ℕ) : Std.Total (keyLE f) := ⟨fun a b => Nat.le_total (f a) (f b)⟩

private instance (f : α → ℕ) : IsTrans α (keyLE f) := ⟨fun _ _ _ => Nat.le_trans⟩

/-- Exchange `k` and `k + 1`. -/
private def swapAdj (k j : ℕ) : ℕ := if j = k then k + 1 else if j = k + 1 then k else j

private theorem swapAdj_le_swapAdj (k : ℕ) {i j : ℕ} (hij : i + 1 < j) :
    swapAdj k i ≤ swapAdj k j := by
  unfold swapAdj
  split_ifs <;> omega

private theorem min_eq_of_ne (k x y : ℕ) (h : decide (x ≤ y) ≠ decide (swapAdj k x ≤ swapAdj k y)) :
    min x y = k := by
  by_contra hmin
  apply h
  rw [decide_eq_decide]
  unfold swapAdj
  split_ifs <;> omega

/-- Both interleaved lists are sorted under the key `g ∘ f`, whenever `g` is monotone on
indices that are at least two apart and `f` recovers the indices. -/
private theorem pairwise_interleaved (e : ℕ ↪ α) (n : ℕ) (f : α → ℕ)
    (hf : Function.LeftInverse f e) (g : ℕ → ℕ) (hg : ∀ i j, i + 1 < j → g i ≤ g j) :
    (interleaved e n).1.Pairwise (keyLE (g ∘ f)) ∧
      (interleaved e n).2.Pairwise (keyLE (g ∘ f)) := by
  simp only [interleaved, List.pairwise_map, keyLE, Function.comp_apply, hf _]
  exact ⟨(List.pairwise_lt_range).imp fun h => hg _ _ (by omega),
    (List.pairwise_lt_range).imp fun h => hg _ _ (by omega)⟩

/-! ## The lower bound -/

/-- **Lower bound for merging.** Any correct comparison-based merging program makes at least
`n - 1` comparisons on the interleaved input with `n` elements, whose two lists have lengths
`⌈n / 2⌉` and `⌊n / 2⌋`, when elements are compared by their index. -/
theorem IsMerger.sub_one_le_countQueries
    {merge : List α → List α → FreeM (LEQuery α) (List α)} (hmerge : IsMerger merge)
    (e : ℕ ↪ α) (f : α → ℕ) (hf : Function.LeftInverse f e) (n : ℕ) :
    n - 1 ≤ (merge (interleaved e n).1 (interleaved e n).2).countQueries
      (LEQuery.oracleOf fun a b => decide (f a ≤ f b)) := by
  classical
  set xs := (interleaved e n).1
  set ys := (interleaved e n).2
  set oracle : {ι : Type} → LEQuery α ι → ι := LEQuery.oracleOf fun a b => decide (f a ≤ f b)
  -- The smaller key of a comparison.
  let low : α × α → ℕ := fun q => min (f q.1) (f q.2)
  have hsub : Finset.range (n - 1) ⊆ ((comparisons oracle (merge xs ys)).map low).toFinset := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hid := pairwise_interleaved e n f hf id fun _ _ h => by simp; omega
    have hsw := pairwise_interleaved e n f hf (swapAdj k) fun _ _ h => swapAdj_le_swapAdj k h
    obtain ⟨q, hq, hne⟩ := hmerge.exists_comparison_ne xs ys oracle
      (LEQuery.oracleOf fun a b => decide (swapAdj k (f a) ≤ swapAdj k (f b)))
      (keyLE (id ∘ f)) (keyLE (swapAdj k ∘ f)) (fun _ _ => rfl) (fun _ _ => rfl)
      hid.1 hid.2 hsw.1 hsw.2 (mem_interleaved e (j := k) (by omega))
      (mem_interleaved e (j := k + 1) (by omega)) (fun h => by simpa using e.injective h)
      (by simp [keyLE, hf _, swapAdj]) (by simp [keyLE, hf _])
    refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, ?_⟩)
    exact min_eq_of_ne k _ _ hne
  calc n - 1
      = (Finset.range (n - 1)).card := (Finset.card_range _).symm
    _ ≤ ((comparisons oracle (merge xs ys)).map low).toFinset.card := Finset.card_le_card hsub
    _ ≤ ((comparisons oracle (merge xs ys)).map low).length := List.toFinset_card_le _
    _ = (merge xs ys).countQueries oracle := by simp

/-- Any correct merging program on an infinite type has query complexity at least `n - 1` on
inputs with `n` elements in total. -/
theorem IsMerger.lowerBound [Infinite α]
    {merge : List α → List α → FreeM (LEQuery α) (List α)} (hmerge : IsMerger merge) :
    LowerBound (fun p : List α × List α => merge p.1 p.2) (fun p => p.1.length + p.2.length)
      (· - 1) := by
  intro n
  let e := Infinite.natEmbedding α
  refine ⟨interleaved e n, by simp; omega,
    LEQuery.oracleOf fun a b => decide (Function.invFun e a ≤ Function.invFun e b), ?_⟩
  exact hmerge.sub_one_le_countQueries e (Function.invFun e)
    (Function.leftInverse_invFun e.injective) n

/-- The standard merge is optimal: on inputs with balanced lengths, no correct merging program
can make fewer comparisons in the worst case. -/
theorem merge_optimal [Infinite α]
    {merge' : List α → List α → FreeM (LEQuery α) (List α)} (hmerge : IsMerger merge') (n : ℕ) :
    ∃ (xs ys : List α), xs.length + ys.length = n ∧ ys.length ≤ xs.length ∧
      xs.length ≤ ys.length + 1 ∧ ∃ (oracle : {ι : Type} → LEQuery α ι → ι),
        ∀ (oracle' : {ι : Type} → LEQuery α ι → ι),
          (merge xs ys).countQueries oracle' ≤ (merge' xs ys).countQueries oracle := by
  let e := Infinite.natEmbedding α
  refine ⟨(interleaved e n).1, (interleaved e n).2, by simp; omega, by simp; omega,
    by simp; omega,
    LEQuery.oracleOf fun a b => decide (Function.invFun e a ≤ Function.invFun e b),
    fun oracle' => ?_⟩
  refine (merge_countQueries_le_sub_one oracle' _ _).trans ?_
  have hlen : (interleaved e n).1.length + (interleaved e n).2.length - 1 = n - 1 := by
    simp only [length_interleaved_fst, length_interleaved_snd]
    omega
  rw [hlen]
  exact hmerge.sub_one_le_countQueries e (Function.invFun e)
    (Function.leftInverse_invFun e.injective) n

end Cslib.Query
