module

public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Dimension.Basic

public import Pdl.Semantics
public import Pdl.Vocab
public import PdlTestFree.Paths

@[expose] public section

/-! # Semilinearity of `L α` for programs over a single atomic program

For a test-free program `α` the set `L α = {n | L α n}` of possible execution lengths of `α`
(see `PdlTestFree.Paths`) is semilinear (`L_isSemilinearSet`); no assumption on the
vocabulary is needed for this.

Conversely, not every semilinear `X ⊆ ℕ` is `L α` for a test-free `α` with `voc α = {a}`:
a test-free `α` always admits some positive number of steps (`L_pos`), so `∅` and `{0}` are
not of this form, and if it admits `0` steps then it admits all multiples of some `p > 0`
(`L_zero`), so e.g. `{0, 2}` is not of this form either. These are the only obstructions:
`exists_L_eq_iff` characterises the sets `L α` as the nonempty semilinear sets `X` such that
`0 ∈ X` implies `k * p ∈ X` for all `k`, for some `p > 0`. -/

open Set Pointwise AddSubmonoid
open scoped Finset

/-! ## `L` of compound programs as set operations -/

lemma L_atom_set (c : ℕ) : {n | L (·c) n} = {1} := by
  ext n
  simp only [mem_ofPred_eq, L, mem_singleton_iff]

lemma L_seq_set (α β : Program) : {n | L (α ;' β) n} = {n | L α n} + {n | L β n} := by
  ext n
  simp only [mem_ofPred_eq, L, mem_add]
  constructor
  · rintro ⟨i, j, hi, hj, rfl⟩; exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩; exact ⟨i, j, hi, hj, rfl⟩

lemma L_union_set (α β : Program) : {n | L (α ⋓ β) n} = {n | L α n} ∪ {n | L β n} := by
  ext n
  simp only [mem_ofPred_eq, L, mem_union]

lemma L_star_set (α : Program) : {n | L (∗α) n} = (closure {n | L α n} : Set ℕ) := by
  ext n
  simp only [mem_ofPred_eq, L, SetLike.mem_coe]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact list_sum_mem fun i hi => subset_closure (hl i hi)
  · intro h
    obtain ⟨l, hl, rfl⟩ := exists_list_of_mem_closure h
    exact ⟨l, hl, rfl⟩

/-! ## Every `L α` is semilinear -/

/-- For any test-free program `α` the set `L α` is semilinear. -/
theorem L_isSemilinearSet : ∀ α : Program, α.testFree → IsSemilinearSet {n | L α n}
  | ?'_, hα => by simp only [Program.testFree] at hα
  | ·c, _ => by
      rw [L_atom_set]
      simp
  | α ;' β, hαβ => by
      simp only [Program.testFree] at hαβ
      rw [L_seq_set]
      exact (L_isSemilinearSet α hαβ.1).add (L_isSemilinearSet β hαβ.2)
  | α ⋓ β, hαβ => by
      simp only [Program.testFree] at hαβ
      rw [L_union_set]
      exact (L_isSemilinearSet α hαβ.1).union (L_isSemilinearSet β hαβ.2)
  | ∗α, hα => by
      simp only [Program.testFree] at hα
      rw [L_star_set]
      exact (L_isSemilinearSet α hα).closure

/-! ## Two obstructions to the converse -/

/-- A test-free program admits some positive number of steps. -/
theorem L_pos : ∀ α : Program, α.testFree → ∃ n, 0 < n ∧ L α n
  | ?'_, hα => by simp only [Program.testFree] at hα
  | ·_, _ => ⟨1, one_pos, rfl⟩
  | α ;' β, hαβ => by
      simp only [Program.testFree] at hαβ
      obtain ⟨i, hi, hLi⟩ := L_pos α hαβ.1
      obtain ⟨j, hj, hLj⟩ := L_pos β hαβ.2
      exact ⟨i + j, by omega, i, j, hLi, hLj, rfl⟩
  | α ⋓ β, hαβ => by
      simp only [Program.testFree] at hαβ
      obtain ⟨i, hi, hLi⟩ := L_pos α hαβ.1
      exact ⟨i, hi, Or.inl hLi⟩
  | ∗α, hα => by
      simp only [Program.testFree] at hα
      obtain ⟨i, hi, hLi⟩ := L_pos α hα
      exact ⟨i, hi, [i], by simpa, by simp⟩

/-- If a test-free program admits `0` steps, then it admits all multiples of some `p > 0`. -/
theorem L_zero : ∀ α : Program, α.testFree → L α 0 → ∃ p, 0 < p ∧ ∀ k, L α (k * p)
  | ?'_, hα, _ => by simp only [Program.testFree] at hα
  | ·c, _, h0 => by simp [L] at h0
  | α ;' β, hαβ, h0 => by
      simp only [Program.testFree] at hαβ
      obtain ⟨i, j, hi, hj, hij⟩ := h0
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
      obtain ⟨p, hp, hLp⟩ := L_zero α hαβ.1 hi
      exact ⟨p, hp, fun k => ⟨k * p, 0, hLp k, hj, by simp⟩⟩
  | α ⋓ β, hαβ, h0 => by
      simp only [Program.testFree] at hαβ
      rcases h0 with h0 | h0
      · obtain ⟨p, hp, hLp⟩ := L_zero α hαβ.1 h0
        exact ⟨p, hp, fun k => Or.inl (hLp k)⟩
      · obtain ⟨p, hp, hLp⟩ := L_zero β hαβ.2 h0
        exact ⟨p, hp, fun k => Or.inr (hLp k)⟩
  | ∗α, hα, _ => by
      simp only [Program.testFree] at hα
      obtain ⟨p, hp, hLp⟩ := L_pos α hα
      refine ⟨p, hp, fun k => ⟨List.replicate k p, ?_, by simp⟩⟩
      intro i hi
      rw [List.eq_of_mem_replicate hi]
      exact hLp

/-! ## The converse, for the sets without these obstructions -/

/-- `aPow n` is the program `a^(n+1)`, i.e. `a ;' ⋯ ;' a` with `n + 1` copies of `a = ·0`. -/
def aPow : ℕ → Program
  | 0 => ·0
  | n + 1 => ·0 ;' aPow n

@[simp] lemma L_aPow (n m : ℕ) : L (aPow n) m ↔ m = n + 1 := by
  induction n generalizing m with
  | zero => simp [aPow, L]
  | succ n IH =>
      simp only [aPow, L, IH]
      constructor
      · rintro ⟨i, j, rfl, rfl, rfl⟩; ring
      · rintro rfl; exact ⟨1, n + 1, rfl, rfl, by ring⟩

lemma aPow_testFree (n : ℕ) : (aPow n).testFree := by
  induction n <;> simp [aPow, *]

lemma aPow_voc (n : ℕ) : (aPow n).voc = {Sum.inr 0} := by
  induction n <;> simp [aPow, *]

/-- `IsL X`: the set `X ⊆ ℕ` is `L α` for a test-free program `α` with `voc α = {a}`. -/
def IsL (X : Set ℕ) : Prop :=
  ∃ α : Program, α.testFree ∧ α.voc = {Sum.inr 0} ∧ {n | L α n} = X

lemma IsL.union {X Y : Set ℕ} (hX : IsL X) (hY : IsL Y) : IsL (X ∪ Y) := by
  obtain ⟨α, hα, hvα, rfl⟩ := hX
  obtain ⟨β, hβ, hvβ, rfl⟩ := hY
  exact ⟨α ⋓ β, ⟨hα, hβ⟩, by simp [hvα, hvβ], L_union_set α β⟩

lemma IsL.add {X Y : Set ℕ} (hX : IsL X) (hY : IsL Y) : IsL (X + Y) := by
  obtain ⟨α, hα, hvα, rfl⟩ := hX
  obtain ⟨β, hβ, hvβ, rfl⟩ := hY
  exact ⟨α ;' β, ⟨hα, hβ⟩, by simp [hvα, hvβ], L_seq_set α β⟩

lemma IsL.closure {X : Set ℕ} (hX : IsL X) : IsL (closure X : Set ℕ) := by
  obtain ⟨α, hα, hvα, rfl⟩ := hX
  exact ⟨∗α, hα, by simp [hvα], L_star_set α⟩

lemma IsL.singleton_succ (n : ℕ) : IsL {n + 1} :=
  ⟨aPow n, aPow_testFree n, aPow_voc n, by ext m; simp⟩

lemma IsL.singleton_of_pos {n : ℕ} (hn : 0 < n) : IsL {n} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact IsL.singleton_succ m

/-- The positive part of a proper linear subset of `ℕ` is empty or `IsL`. -/
lemma IsProperLinearSet.isL_diff_zero {s : Set ℕ} (hs : IsProperLinearSet s) :
    s \ {0} = ∅ ∨ IsL (s \ {0}) := by
  rw [isProperLinearSet_iff] at hs
  obtain ⟨a, t, ht, rfl⟩ := hs
  have hcard : #t ≤ 1 := by simpa [CommSemiring.rank_self] using ht.cardinal_le_rank
  simp_rw [Finset.card_le_one_iff_subset_singleton, Finset.subset_singleton_iff] at hcard
  rcases hcard with ⟨b, (rfl | rfl)⟩
  · -- `s = {a}`
    have hs : a +ᵥ (closure ((∅ : Finset ℕ) : Set ℕ) : Set ℕ) = {a} := by
      ext n; simp
    rw [hs]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · left; simp
    · right
      rw [sdiff_singleton_eq_self (by simpa using ha.ne)]
      exact IsL.singleton_of_pos ha
  · -- `s = a + bℕ` with `b ≠ 0`
    have hb : b ≠ 0 := by simpa [ne_comm] using ht.zero_notMem_image
    have hb' : 0 < b := Nat.pos_of_ne_zero hb
    right
    have hmem : ∀ n,
        n ∈ a +ᵥ (closure (({b} : Finset ℕ) : Set ℕ) : Set ℕ) ↔ ∃ m, a + m * b = n := by
      intro n
      simp only [Finset.coe_singleton, mem_vadd_set, SetLike.mem_coe,
        AddSubmonoid.mem_closure_singleton, smul_eq_mul, vadd_eq_add, exists_exists_eq_and]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · -- `bℕ \ {0} = {b} + bℕ`
      convert (IsL.singleton_of_pos hb').add (IsL.singleton_of_pos hb').closure using 1
      ext n
      simp only [mem_sdiff, hmem, mem_singleton_iff, mem_add, SetLike.mem_coe,
        AddSubmonoid.mem_closure_singleton, smul_eq_mul, zero_add]
      constructor
      · rintro ⟨⟨m, rfl⟩, hm⟩
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 :=
          Nat.exists_eq_add_one_of_ne_zero (by rintro rfl; simp at hm)
        exact ⟨b, rfl, m * b, ⟨m, rfl⟩, by ring⟩
      · rintro ⟨x, rfl, y, ⟨m, rfl⟩, rfl⟩
        exact ⟨⟨m + 1, by ring⟩, (Nat.add_pos_left hb' _).ne'⟩
    · -- `(a + bℕ) \ {0} = {a} + bℕ`
      convert (IsL.singleton_of_pos ha).add (IsL.singleton_of_pos hb').closure using 1
      ext n
      simp only [mem_sdiff, hmem, mem_singleton_iff, mem_add, SetLike.mem_coe,
        AddSubmonoid.mem_closure_singleton, smul_eq_mul]
      constructor
      · rintro ⟨⟨m, rfl⟩, -⟩
        exact ⟨a, rfl, m * b, ⟨m, rfl⟩, rfl⟩
      · rintro ⟨x, rfl, y, ⟨m, rfl⟩, rfl⟩
        exact ⟨⟨m, rfl⟩, (Nat.add_pos_left ha _).ne'⟩

/-- The positive part of a semilinear subset of `ℕ` is empty or `IsL`. -/
lemma IsSemilinearSet.isL_diff_zero {X : Set ℕ} (hX : IsSemilinearSet X) :
    X \ {0} = ∅ ∨ IsL (X \ {0}) := by
  obtain ⟨S, hS, rfl⟩ := isProperSemilinearSet_iff.mp hX.isProperSemilinearSet
  clear hX
  induction S using Finset.induction_on with
  | empty => left; simp
  | insert t S _ IH =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hS
      rw [Finset.coe_insert, sUnion_insert, union_sdiff_distrib]
      rcases hS.1.isL_diff_zero with h1 | h1 <;> rcases IH hS.2 with h2 | h2
      · left; rw [h1, h2, union_empty]
      · right; rwa [h1, empty_union]
      · right; rwa [h2, union_empty]
      · right; exact h1.union h2

/-- The sets `L α` for test-free `α` with `voc α = {a}` are exactly the nonempty semilinear
sets `X ⊆ ℕ` such that, if `0 ∈ X`, then `X` contains all multiples of some `p > 0`. -/
theorem exists_L_eq_iff (X : Set ℕ) :
    (∃ α : Program, α.testFree ∧ α.voc = {Sum.inr 0} ∧ {n | L α n} = X) ↔
    IsSemilinearSet X ∧ X.Nonempty ∧ (0 ∈ X → ∃ p, 0 < p ∧ ∀ k, k * p ∈ X) := by
  constructor
  · rintro ⟨α, hα, -, rfl⟩
    refine ⟨L_isSemilinearSet α hα, ?_, ?_⟩
    · obtain ⟨n, -, hn⟩ := L_pos α hα
      exact ⟨n, hn⟩
    · intro h0
      obtain ⟨p, hp, hLp⟩ := L_zero α hα h0
      exact ⟨p, hp, hLp⟩
  · rintro ⟨hX, hne, h0⟩
    rcases hX.isL_diff_zero with h | h
    · -- then `X ⊆ {0}`, so `X = {0}`, which is excluded
      exfalso
      rw [sdiff_eq_empty] at h
      obtain ⟨x, hx⟩ := hne
      obtain rfl : x = 0 := h hx
      obtain ⟨p, hp, hLp⟩ := h0 hx
      have := h (hLp 1)
      simp at this
      omega
    · by_cases h0X : 0 ∈ X
      · obtain ⟨p, hp, hLp⟩ := h0 h0X
        obtain ⟨α, hα, hv, hL⟩ := h.union (IsL.singleton_of_pos hp).closure
        refine ⟨α, hα, hv, ?_⟩
        rw [hL]
        ext n
        simp only [mem_union, mem_sdiff, mem_singleton_iff, SetLike.mem_coe,
          AddSubmonoid.mem_closure_singleton, smul_eq_mul]
        constructor
        · rintro (⟨hn, -⟩ | ⟨k, rfl⟩)
          · exact hn
          · exact hLp k
        · intro hn
          by_cases hn0 : n = 0
          · exact Or.inr ⟨0, by simp [hn0]⟩
          · exact Or.inl ⟨hn, hn0⟩
      · rwa [sdiff_singleton_eq_self h0X] at h
