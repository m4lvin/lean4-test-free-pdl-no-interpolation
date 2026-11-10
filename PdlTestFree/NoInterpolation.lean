module

public import Pdl.Bisimulation
public import Pdl.Discon
public import Pdl.Interpolation.Statement

public import PdlTestFree.Paths

@[expose] public section

-- Verso syntax (instead of Markdown) for `$$` math below.
set_option doc.verso.module true
-- Suggestions are off because they fire on every code span.
set_option doc.verso.suggestions false

/-! # Test-free PDL does not have Craig interpolation

This file gives a valid implication between *test-free* PDL formulas that has no test-free
interpolant. The statement is purely semantic: it does not depend on the tableau system or
on the method used to construct interpolants elsewhere in this project.

Write `p, q, s` for the proposition letters `·0, ·1, ·2` and `a` for the atomic program
`·0`, and let

* `Γ₁ = { s, [a*]((p ∧ s) → (⟨a⟩⊤ ∧ [a]s)) }`
* `Γ₂ = { [a*](q → p), [a*](⟨a⟩q → q), ⟨a*⟩(q ∧ [a]⊥) }`

Both sets are test-free.
The common vocabulary is `{a, p}`; the `s` occurs only in `Γ₁`, the `q` only in `Γ₂`.

`Γ₁ ∪ Γ₂` is unsatisfiable (`gammaOne_gammaTwo_unsat`), i.e. `⋀Γ₁ → ¬⋀Γ₂` is valid: the last
formula of `Γ₂` gives a path to a `q`-state without successors; by `[a*](⟨a⟩q → q)` every
state on that path is a `q`-state, and by `[a*](q → p)` also a `p`-state.
By induction along the path, using `s` at the start and `p ∧ s → ⟨a⟩⊤ ∧ [a]s` from `Γ₁`,
every state on the path satisfies `s`; so the last state satisfies `p ∧ s` and must have
a successor, which it does not.

After projecting away the private letters, `Γ₁` says "along every `a`-path, as long as `p`
has held there is a further `a`-step" (no all-`p` path ends in a dead end) and `Γ₂` says
"some all-`p` path ends in a dead end". An interpolant has to separate these two
"until"-like properties, which needs a test: `[(p?;a)*](p → ⟨a⟩⊤)` is an interpolant
(`withTest_Interpolant`), but no test-free formula is. We make this precise with a
single Kripke model `MG` and two of its states `m` and `v j` such that

* `(MG, m) ⊨ Γ₁` (`gammaOne_at_m`),
* `(MG, v j) ⊨ Γ₂` for every `j` (`gammaTwo_at_v`),
* `m` and `v j` satisfy the same test-free formulas over `{a, p}` of modal depth `≤ j`
  (`depth_equiv`).

Hence no test-free formula `θ` over `{a, p}` satisfies `Γ₁ ⊨ θ` and `Γ₂ ⊨ ¬θ`
(`no_interpolant`). Three letters are the minimum for this kind of example:
a side without private vocabulary is, up to negation, itself an interpolant.

## The model `MG`

(A picture of the model can be found in the paper.)

`MG` has the states `u`, `m`, `w i` and `v i` for `i : ℕ`. The only atomic program with a
nonempty relation is `a`; its relation `R` is

* `u → x` for every state `x` off the chain, that is, for every `x` other than the `v i`,
* `m → u`, `m → m`,
* `w (i+1) → u, w i` and `v (i+1) → u, v i`,
* `w 0` and `v 0` have no successors.

Valuation: `p` at `m`, at every `w i` and at every `v i`; `s` at `m` and `u`; `q` at
every `v i` (nothing else at `u`).

The chain `v j → v (j-1) → … → v 0` is an all-`p` path to the dead end `v 0`, and no edge
leads from a state off the chain into it, so `q := {v i}` satisfies `Γ₂` at `v j`. The
states off the chain are therefore exactly those reachable from `m`, and there, with
`s := {m, u}`, `Γ₁` holds at `m`.

## Why `m` and `v j` agree on test-free formulas of depth `≤ j`

With a single atomic program, a *test-free* program `α` relates `w` to `v` iff for some
`n` such that `α` can be executed by exactly `n` actual steps (`L α n`), there is a path of
exactly `n` steps from `w` to `v` (`relate_iff`). So `[α]ψ` at `w` quantifies over the states
reachable in exactly `n` steps, for those `n` (`box_iff`). These sets are

$$`
      \begin{array}{llll}
        n          & \text{from } m                   & \text{from } v_k                          \\
        \hline
        0          & \{ m \}                          & \{ v_k \}                                 \\
        1          & \{ m, u \}                       & \{ u, v_{k-1} \}                          \\
        2 \ldots k & \{ m, u \} \cup \text{all $w_i$} & \{ m, u, v_{k-n} \} \cup \text{all $w_i$} \\
        k+1 \ldots & \{ m, u \} \cup \text{all $w_i$} & \{ m, u \} \cup \text{all $w_i$}          \\
      \end{array}`

since `u` reaches every state off the chain in every number `≥ 1` of steps, while `v 0`
reaches nothing. The relation `Z` relating every state to itself and moreover `w i` to
`v i` is a bisimulation of `MG` with itself for the vocabulary `{a, p}` (`Z_isBisim`), and
bisimilar states satisfy the same formulas over that vocabulary (`IsBisim.evaluate` from
`Pdl.Bisimulation`, which does allow tests). Hence, by induction on `ψ` with
`mdepth ψ + 1 ≤ j` (so `j ≥ 1`), in each row the witnesses on both sides are matched: the
states off the chain occur on both sides, the chain states `v j` and `v (j-1)` are
equivalent to `m` by the induction hypothesis, and `v (j-n)` (for `n ≥ 2`) is equivalent
to `w (j-n)` by `Z`, which is reachable from `m` in the same number of steps.
So `[α]ψ` has the same truth value at `m` and at `v j`.

The depth bound is sharp: the test-free formula `⟨a⟩(p ∧ ⟨a⟩(p ∧ … ⟨a⟩(p ∧ [a]⊥)))` with
`j` nested diamonds has depth `j+1`, is true at `v j`, and is false at `m`. The
test-freeness cannot be dropped either: `[(p?;a)*](p → ⟨a⟩⊤)` is false at every
`v j` and true at `m`. -/

namespace TestfreeNoItp

open HasSat vDash

/-! ## The two sets of formulas -/

abbrev p : Formula := ·0
abbrev q : Formula := ·1
abbrev s : Formula := ·2
abbrev a : Program := ·0

/-- The body of the left star formula: `(p ∧ s) → (⟨a⟩⊤ ∧ [a]s)`.
(A `def`, not an `abbrev`, so that `simp only [evaluate]` leaves it alone.) -/
def body : Formula := (p ⋀ s) ↣ ((~(⌈a⌉⊥)) ⋀ ⌈a⌉s)

/-- `Γ₁ = { s, [a*]((p ∧ s) → (⟨a⟩⊤ ∧ [a]s)) }` -/
def gammaOne : List Formula := [s, ⌈∗a⌉body]

/-- `Γ₂ = { [a*](q → p), [a*](⟨a⟩q → q), ⟨a*⟩(q ∧ [a]⊥) }` -/
def gammaTwo : List Formula :=
  [⌈∗a⌉(q ↣ p), ⌈∗a⌉((~⌈a⌉~q) ↣ q), ~⌈∗a⌉~(q ⋀ ⌈a⌉⊥)]

lemma gammaOne_testFree : ∀ φ ∈ gammaOne, φ.testFree := by
  simp [gammaOne, body]

lemma gammaTwo_testFree : ∀ φ ∈ gammaTwo, φ.testFree := by
  simp [gammaTwo]

/-! ## The implication is valid -/

/-- `Γ₁` at `w`, unfolded: `s` holds at `w`, and every `a*`-reachable `p ∧ s`-state has an
`a`-successor and all its `a`-successors satisfy `s`. -/
lemma gammaOne_iff {W : Type} (M : KripkeModel W) (w : W) :
    (∀ φ ∈ gammaOne, evaluate M w φ) ↔
      M.val w 2 ∧ ∀ v, Relation.ReflTransGen (M.Rel 0) w v → M.val v 0 → M.val v 2 →
        (∃ u, M.Rel 0 v u) ∧ ∀ u, M.Rel 0 v u → M.val u 2 := by
  simp only [gammaOne, body, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, evaluate, relate, not_and, not_not, imp_false, not_forall, exists_prop,
    not_exists, and_imp]

/-- `Γ₂` at `w`, unfolded: every `a*`-reachable `q`-state is a `p`-state, every
`a*`-reachable state with a `q`-successor is a `q`-state, and some `a*`-reachable `q`-state
has no `a`-successor. -/
lemma gammaTwo_iff {W : Type} (M : KripkeModel W) (w : W) :
    (∀ φ ∈ gammaTwo, evaluate M w φ) ↔
      (∀ v, Relation.ReflTransGen (M.Rel 0) w v → M.val v 1 → M.val v 0) ∧
      (∀ v, Relation.ReflTransGen (M.Rel 0) w v → ∀ u, M.Rel 0 v u → M.val u 1 → M.val v 1) ∧
      (∃ v, Relation.ReflTransGen (M.Rel 0) w v ∧ M.val v 1 ∧ ∀ u, ¬ M.Rel 0 v u) := by
  simp only [gammaTwo, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, evaluate, relate, not_and, not_not, not_forall, not_exists, exists_prop,
    imp_false, forall_exists_index, and_imp]

/-- By `Γ₂`, any `a*`-reachable `q`-state is reached along `p ∧ q`-states. -/
lemma gammaTwo_path {W : Type} {M : KripkeModel W} {w : W}
    (h2 : ∀ φ ∈ gammaTwo, evaluate M w φ) {v : W}
    (hv : Relation.ReflTransGen (M.Rel 0) w v) (hq : M.val v 1) :
    Relation.ReflTransGen (fun x y => M.Rel 0 x y ∧ M.val x 0 ∧ M.val x 1) w v := by
  obtain ⟨hqp, hcl, -⟩ := (gammaTwo_iff M w).mp h2
  induction hv with
  | refl => exact .refl
  | @tail v u hwv hvu IH =>
      have hqv : M.val v 1 := hcl v hwv u hvu hq
      exact .tail (IH hqv) ⟨hvu, hqp v hwv hqv, hqv⟩

/-- `Γ₁ ∪ Γ₂` is not satisfiable. -/
theorem gammaOne_gammaTwo_unsat : ¬ satisfiable (gammaOne ++ gammaTwo) := by
  rintro ⟨W, M, w, hw⟩
  have h1 : ∀ φ ∈ gammaOne, evaluate M w φ := fun φ hφ => hw φ (by simp [hφ])
  have h2 : ∀ φ ∈ gammaTwo, evaluate M w φ := fun φ hφ => hw φ (by simp [hφ])
  obtain ⟨hs, hbody⟩ := (gammaOne_iff M w).mp h1
  obtain ⟨hqp, -, v, hv, hqv, hdead⟩ := (gammaTwo_iff M w).mp h2
  -- by `Γ₂` the path to `v` consists of `p ∧ q`-states, so by `Γ₁` all of them satisfy `s`
  have hsv : M.val v 2 := by
    suffices ∀ x, Relation.ReflTransGen (fun x y => M.Rel 0 x y ∧ M.val x 0 ∧ M.val x 1) w x →
        Relation.ReflTransGen (M.Rel 0) w x ∧ M.val x 2 from (this v (gammaTwo_path h2 hv hqv)).2
    intro x hx
    induction hx with
    | refl => exact ⟨.refl, hs⟩
    | tail _ hxu IH => exact ⟨IH.1.tail hxu.1, (hbody _ IH.1 hxu.2.1 IH.2).2 _ hxu.1⟩
  -- so `v` satisfies `p ∧ s` and must have a successor, but it has none
  obtain ⟨u, hu⟩ := (hbody v hv (hqp v hv hqv) hsv).1
  exact hdead u hu

/-- Thus `⋀Γ₁ → ¬⋀Γ₂` is valid. -/
theorem gammaOne_gammaTwo_taut : tautology (con gammaOne ↣ ~con gammaTwo) := by
  intro W M w
  simp only [evaluate, conEval, not_and, not_not]
  intro h1 h2
  refine gammaOne_gammaTwo_unsat ⟨W, M, w, fun φ hφ => ?_⟩
  simp only [List.mem_append] at hφ
  rcases hφ with hφ | hφ
  · exact h1 φ hφ
  · exact h2 φ hφ

/-! ## The model `MG` -/

/-- States of `MG`: the states `u`, `m` and `w i` off the `q`-chain, and the chain `v i`. -/
inductive St : Type
  | u : St
  | m : St
  | w : ℕ → St
  | v : ℕ → St
  deriving DecidableEq

open St

/-- Valuation of `MG`. Letters: `p = 0`, `q = 1`, `s = 2`. -/
def val : St → ℕ → Prop
  | u, n => n = 2
  | m, n => n = 0 ∨ n = 2
  | w _, n => n = 0
  | v _, n => n = 0 ∨ n = 1

/-- The relation of `a` in `MG`: `u` sees every state off the chain, `m` sees `u` and
itself, and the two chains lead down to their dead ends `w 0` and `v 0`. -/
def R : St → St → Prop
  | u, v _ => False
  | u, _ => True
  | m, y => y = u ∨ y = m
  | w (i + 1), y => y = u ∨ y = w i
  | w 0, _ => False
  | v (i + 1), y => y = u ∨ y = v i
  | v 0, _ => False

/-- The model `MG`: the atomic program `a = ·0` has the relation `R`, all other atomic
programs have the empty relation. -/
def MG : KripkeModel St := ⟨val, fun | 0 => R | _ + 1 => fun _ _ => False⟩

@[simp] lemma MG_val (x : St) (n : ℕ) : MG.val x n ↔ val x n := Iff.rfl
@[simp] lemma MG_Rel_zero : MG.Rel 0 = R := rfl

/-! ### The states off the `q`-chain

No edge leads from `u`, `m` or a `w i` into the chain, so these are exactly the states
reachable from `m`, and they form the part of `MG` where `Γ₁` holds. -/

/-- The states off the `q`-chain: `u`, `m` and the `w i`. -/
@[simp]
def offChain : St → Prop
  | v _ => False
  | _ => True

lemma R_u {y : St} (hy : offChain y) : R u y := by cases y <;> simp_all [R]

lemma offChain_R {x y : St} (hx : offChain x) (h : R x y) : offChain y := by
  cases x with
  | u => cases y <;> simp_all [R]
  | m => rcases h with rfl | rfl <;> simp
  | w i =>
      cases i with
      | zero => exact h.elim
      | succ i => rcases h with rfl | rfl <;> simp
  | v i => exact hx.elim

lemma NStep_offChain {n : ℕ} {x y : St} (hx : offChain x) (h : NStep R n x y) :
    offChain y := by
  induction n generalizing x with
  | zero => simp only [NStep_zero] at h; subst h; exact hx
  | succ n IH => obtain ⟨z, hz, hzy⟩ := h; exact IH (offChain_R hx hz) hzy

/-! ### Reachability in `M` -/

/-- From `u`, every state off the chain is reached in any number `n ≥ 1` of steps. -/
lemma u_NStep (y : St) (hy : offChain y) : ∀ n, 1 ≤ n → NStep R n u y := by
  intro n hn
  induction n with
  | zero => omega
  | succ n IH =>
      cases n with
      | zero => exact ⟨y, R_u hy, rfl⟩
      | succ n => exact ⟨u, R_u (by simp), IH (by omega)⟩

/-- From `m`, every state off the chain is reached in any number `n ≥ 2` of steps. -/
lemma m_NStep (y : St) (hy : offChain y) {n : ℕ} (hn : 2 ≤ n) : NStep R n m y := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact ⟨u, Or.inl rfl, u_NStep y hy k (by omega)⟩

lemma NStep_one_m {y : St} : NStep R 1 m y ↔ y = u ∨ y = m := by
  simp only [NStep_succ, NStep_zero]
  constructor
  · rintro ⟨z, h, rfl⟩; exact h
  · intro h; exact ⟨y, h, rfl⟩

/-- From `v j` with `j ≥ 1`, every state off the chain is reached in any number `n ≥ 2`
of steps. -/
lemma v_NStep (y : St) (hy : offChain y) {j n : ℕ} (hj : 1 ≤ j) (hn : 2 ≤ n) :
    NStep R n (v j) y := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact ⟨u, Or.inl rfl, u_NStep y hy k (by omega)⟩

/-- A state off the chain reached from `v j` in `n` steps is also reached from `m` in `n`
steps. -/
lemma NStep_m_of_v {n j : ℕ} {y : St} (hy : offChain y) (h : NStep R n (v j) y) :
    NStep R n m y := by
  rcases n with _ | _ | n
  · simp only [NStep_zero] at h; subst h; simp at hy
  · obtain ⟨z, hz, hzy⟩ := h
    simp only [NStep_zero] at hzy
    subst hzy
    rw [NStep_one_m]
    cases j with
    | zero => exact hz.elim
    | succ j =>
        rcases hz with rfl | rfl
        · exact Or.inl rfl
        · simp at hy
  · exact m_NStep y hy (by omega)

/-- A state on the chain reached from `v j` in `n` steps is `v (j - n)`, with `n ≤ j`. -/
lemma NStep_v_chain {n : ℕ} : ∀ {j i : ℕ}, NStep R n (v j) (v i) → n ≤ j ∧ i = j - n := by
  induction n with
  | zero => intro j i h; simp only [NStep_zero, St.v.injEq] at h; omega
  | succ n IH =>
      intro j i h
      obtain ⟨z, hz, hzi⟩ := h
      cases j with
      | zero => exact hz.elim
      | succ j =>
          rcases hz with rfl | rfl
          · have := NStep_offChain (x := u) (by simp) hzi
            simp at this
          · obtain ⟨h1, h2⟩ := IH hzi
            exact ⟨by omega, by omega⟩

/-! ## The bisimulation of `MG` with itself -/

/-- The common vocabulary `{a, p}`: the proposition letter `p = ·0` and the atomic
program `a = ·0`. -/
def commonVoc : Vocab := {Sum.inl 0, Sum.inr 0}

/-- The common vocabulary of `⋀Γ₁` and `¬⋀Γ₂` is `{a, p}`. -/
lemma voc_gammaOne_gammaTwo : (con gammaOne).voc ∩ (~con gammaTwo).voc = commonVoc := by
  decide

/-- The bisimulation: every state is related to itself, and moreover `w i` to `v i`. -/
def Z (x y : St) : Prop := x = y ∨ (∃ i, x = w i ∧ y = v i)

lemma Z_rfl (x : St) : Z x x := Or.inl rfl
lemma Z_w_v (i : ℕ) : Z (w i) (v i) := Or.inr ⟨i, rfl, rfl⟩

/-- `Z` is a bisimulation of `MG` with itself for the common vocabulary `{a, p}`. -/
theorem Z_isBisim : IsBisim MG MG Z commonVoc where
  atoms := by
    intro x y hxy n hn
    obtain rfl : n = 0 := by simpa [commonVoc, Vocab.atomProps] using hn
    rcases hxy with rfl | ⟨i, rfl, rfl⟩
    · rfl
    · simp [val]
  zig := by
    intro x y hxy c hc x' hxx'
    obtain rfl : c = 0 := by simpa [commonVoc, Vocab.atomProgs] using hc
    rcases hxy with rfl | ⟨i, rfl, rfl⟩
    · exact ⟨x', hxx', Z_rfl x'⟩
    · cases i with
      | zero => exact hxx'.elim
      | succ i =>
          rcases hxx' with rfl | rfl
          · exact ⟨u, Or.inl rfl, Z_rfl u⟩
          · exact ⟨v i, Or.inr rfl, Z_w_v i⟩
  zag := by
    intro x y hxy c hc y' hyy'
    obtain rfl : c = 0 := by simpa [commonVoc, Vocab.atomProgs] using hc
    rcases hxy with rfl | ⟨i, rfl, rfl⟩
    · exact ⟨y', hyy', Z_rfl y'⟩
    · cases i with
      | zero => exact hyy'.elim
      | succ i =>
          rcases hyy' with rfl | rfl
          · exact ⟨u, Or.inl rfl, Z_rfl u⟩
          · exact ⟨w i, Or.inr rfl, Z_w_v i⟩

/-- The chains `w i` and `v i` agree on all `{a, p}`-formulas. -/
lemma eval_w_v {φ : Formula} (hφ : φ.voc ⊆ commonVoc) (i : ℕ) :
    evaluate MG (w i) φ ↔ evaluate MG (v i) φ :=
  Z_isBisim.evaluate φ hφ _ _ (Z_w_v i)

/-! ## Depth-bounded equivalence of `m` and `v j` -/

/-- The claim proved by induction in the proof of `depth_equiv`: the states `m` and `v k`
agree on any test-free formula `φ` over the common vocabulary `{a, p}`, for any `k` from the
modal depth of `φ` onwards. -/
theorem depth_equiv_claim : ∀ (φ : Formula), φ.testFree → φ.voc ⊆ commonVoc →
    ∀ k, mdepth φ ≤ k → (evaluate MG m φ ↔ evaluate MG (v k) φ)
  | ⊥, _, _, _, _ => Iff.rfl
  | ·n, _, hv, k, _ => by
      obtain rfl : n = 0 := by
        simpa [commonVoc] using hv (by simp : Sum.inl n ∈ (·n : Formula).voc)
      simp [val]
  | ~φ, hf, hv, k, hk => by
      simp only [Formula.testFree] at hf
      simp only [evaluate]
      rw [depth_equiv_claim φ hf hv k hk]
  | φ ⋀ ψ, hf, hv, k, hk => by
      simp only [Formula.testFree] at hf
      simp only [Formula.voc, Finset.union_subset_iff] at hv
      simp only [evaluate]
      simp only [mdepth, max_le_iff] at hk
      rw [depth_equiv_claim φ hf.1 hv.1 k hk.1, depth_equiv_claim ψ hf.2 hv.2 k hk.2]
  | ⌈α⌉ ψ, hf, hv, k, hk => by
      simp only [Formula.testFree] at hf
      obtain ⟨hα, hψ⟩ := hf
      simp only [Formula.voc, Finset.union_subset_iff] at hv
      -- `α` is test-free over `{a, p}`, so `voc α ⊆ {a}`
      have hvα : α.voc ⊆ {Sum.inr 0} := by
        intro x hx
        obtain ⟨c, rfl⟩ := Program.testFree_voc α hα x hx
        simpa [commonVoc] using hv.1 hx
      simp only [mdepth] at hk
      rw [box_iff MG α hα hvα, box_iff MG α hα hvα, MG_Rel_zero]
      apply forall_congr'; intro n; apply imp_congr_right; intro _
      -- compare the witnesses reached in exactly `n` steps from `m` and from `v k`
      refine Iff.intro ?mp ?mpr
      case mpr =>
        -- from the `m`-column to the `v k`-column
        intro h y hy
        -- here `k ≥ 1`, since `⌈α⌉ψ` has depth at least `1`
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rcases n with _ | _ | n
        · -- `y = m`, matched by `v k`
          simp only [NStep_zero] at hy; subst hy
          rw [depth_equiv_claim ψ hψ hv.2 (j + 1) (by omega)]
          exact h _ rfl
        · -- the witnesses `u` and `m` are matched by `u` and `v (k-1)`
          rcases NStep_one_m.mp hy with rfl | rfl
          · exact h u ⟨u, Or.inl rfl, rfl⟩
          · rw [depth_equiv_claim ψ hψ hv.2 j (by omega)]
            exact h (v j) ⟨v j, Or.inr rfl, rfl⟩
        · -- `n ≥ 2`: `y` is off the chain and also reached from `v k` in `n` steps
          exact h y (v_NStep y (NStep_offChain (by simp) hy) (by omega) (by omega))
      case mp =>
        -- from the `v k`-column to the `m`-column
        intro h y hy
        by_cases hoff : offChain y
        · -- off the chain: `y` is reached from `m` in the same number of steps
          exact h y (NStep_m_of_v hoff hy)
        · -- on the chain: `y = v (k - n)`
          obtain ⟨i, rfl⟩ : ∃ i, y = v i := by cases y <;> simp_all
          obtain ⟨hn, rfl⟩ := NStep_v_chain hy
          rcases n with _ | _ | n
          · -- `y = v k`, matched by `m` itself
            rw [Nat.sub_zero, ← depth_equiv_claim ψ hψ hv.2 k (by omega)]
            exact h m rfl
          · -- `y = v (k-1)`, matched by `m`
            rw [← depth_equiv_claim ψ hψ hv.2 (k - 1) (by omega)]
            exact h m (NStep_one_m.mpr (Or.inr rfl))
          · -- `y = v (k-n)` with `n ≥ 2`, matched by `w (k-n)`
            rw [← eval_w_v hv.2]
            exact h (w _) (m_NStep _ (by simp) (by omega))

/-- **Key lemma.** The states `m` and `v j` agree test-free on `{a, p}` up to `j`, i.e. they
satisfy the same test-free formulas over the common vocabulary of modal depth at most `j`. -/
theorem depth_equiv (j : ℕ) : agree MG commonVoc j m (v j) :=
  fun φ hφ hv hj => depth_equiv_claim φ hφ hv j hj

/-! ## `Γ₁` holds at `m`, `Γ₂` holds at `v j` -/

/-- Every state reachable from a state off the chain is off the chain. -/
lemma offChain_reach {x y : St} (hx : offChain x) (h : Relation.ReflTransGen R x y) :
    offChain y := by
  induction h with
  | refl => exact hx
  | tail _ hstep IH => exact offChain_R IH hstep

theorem gammaOne_at_m : ∀ φ ∈ gammaOne, evaluate MG m φ := by
  rw [gammaOne_iff]
  refine ⟨by simp [val], ?_⟩
  -- the only `a*`-reachable `p ∧ s`-state is `m` itself
  intro y hy hpy hsy
  have hoff : offChain y := offChain_reach (by simp) hy
  cases y with
  | u => simp [val] at hpy
  | m => exact ⟨⟨m, Or.inr rfl⟩, by rintro z (rfl | rfl) <;> simp [val]⟩
  | w i => simp [val] at hsy
  | v i => simp at hoff

/-- The `a`-chain from `v j` down to `v 0`. -/
lemma v_reach_zero (j : ℕ) : Relation.ReflTransGen R (v j) (v 0) := by
  induction j with
  | zero => exact .refl
  | succ j IH => exact .head (Or.inr rfl) IH

theorem gammaTwo_at_v (j : ℕ) : ∀ φ ∈ gammaTwo, evaluate MG (v j) φ := by
  rw [gammaTwo_iff]
  simp only [MG_Rel_zero]
  refine ⟨?_, ?_, v 0, v_reach_zero j, by simp [val], fun _ h => h⟩
  · -- `q → p` is globally true
    intro y _ hqy
    cases y <;> simp_all [val]
  · -- any state with a `q`-successor is a `q`-state
    intro y _ z hyz hqz
    cases y with
    | u => cases z <;> simp_all [R, val]
    | m => rcases hyz with rfl | rfl <;> simp_all [val]
    | w i =>
        cases i with
        | zero => exact hyz.elim
        | succ i => rcases hyz with rfl | rfl <;> simp_all [val]
    | v i => simp [val]

/-- In `MG` we have `m ⊨ Γ₁` and `v j ⊨ Γ₂` for any `j`. -/
theorem model_sat : (MG, m) ⊨ gammaOne ∧ ∀ j, (MG, v j) ⊨ gammaTwo :=
  ⟨gammaOne_at_m, gammaTwo_at_v⟩

/-! ## Main theorem -/

/-- **`Γ₁ ; Γ₂` has no test-free interpolant**: there is no test-free interpolant for
`⋀Γ₁ → ¬⋀Γ₂`. -/
theorem no_interpolant :
    ¬ ∃ θ : Formula, θ.testFree ∧ Interpolant (con gammaOne) (~con gammaTwo) θ := by
  rintro ⟨θ, hθ, hvoc, h1, h2⟩
  rw [voc_gammaOne_gammaTwo] at hvoc
  -- `θ` holds at `m` ...
  have hm : evaluate MG m θ := by
    have := h1 St MG m
    simp only [evaluate, conEval, not_and, not_not] at this
    exact this gammaOne_at_m
  -- ... but not at `v j` where `j` is the modal depth of `θ`
  have hv : ¬ evaluate MG (v (mdepth θ)) θ := by
    have := h2 St MG (v (mdepth θ))
    simp only [evaluate, conEval, not_and, not_not] at this
    exact fun hθ => this hθ (gammaTwo_at_v _)
  exact hv ((depth_equiv (mdepth θ) θ hθ hvoc le_rfl).mp hm)

/-- **Test-free PDL does not have Craig interpolation**: not every valid implication between
test-free formulas has a test-free interpolant. -/
theorem testFree_no_interpolation :
    ¬ ∀ φ ψ : Formula, φ.testFree → ψ.testFree → tautology (φ ↣ ψ) →
      ∃ θ : Formula, θ.testFree ∧ Interpolant φ ψ θ :=
  fun h => no_interpolant (h (con gammaOne) (~con gammaTwo)
    (by simp [gammaOne, body]) (by simp [gammaTwo]) gammaOne_gammaTwo_taut)

end TestfreeNoItp
