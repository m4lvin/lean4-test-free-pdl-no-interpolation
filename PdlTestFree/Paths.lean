module

public import Pdl.Semantics
public import Pdl.Vocab
public import PdlTestFree.Basic

@[expose] public section

/-! # Single-program test-free PDL and execution lengths

Write `a` for the atomic program `·0`. For a test-free program `α` with `voc α = {a}` the
relation of `α` in any Kripke model `M` is determined by the relation of `a` alone: `α`
relates `w` to `v` iff there is an `a`-path from `w` to `v` of exactly `n` steps, for some
possible execution length `n` of `α` (`L α n`). This is `relate_iff`, and `box_iff` is the
resulting characterisation of `[α]φ`.

This is different from `distance` in `Pdl.Local.Distance`, which is the *minimal* number of
atomic steps of an execution; here all possible numbers of steps matter, since `[α]`
quantifies over the endpoints of all of them. The paths also differ from `Walk` there, which
never visits a state twice, whereas the self-loops at `m` and `u` in `PdlTestFree.NoInterpolation`
are exactly what lets us reach a state in every number of steps. -/

section Paths

variable {S : Type}

/-- `NStep R n w v`: `w Rⁿ v`, i.e. there is an `R`-path of exactly `n` steps from `w` to `v`
(states may repeat). -/
def NStep (R : S → S → Prop) : ℕ → S → S → Prop
  | 0, w, v => w = v
  | n + 1, w, v => ∃ u, R w u ∧ NStep R n u v

variable {R : S → S → Prop}

@[simp] lemma NStep_zero {w v : S} : NStep R 0 w v ↔ w = v := Iff.rfl
@[simp] lemma NStep_succ {n : ℕ} {w v : S} :
    NStep R (n + 1) w v ↔ ∃ u, R w u ∧ NStep R n u v := Iff.rfl

lemma NStep_add (i j : ℕ) (w v : S) :
    NStep R (i + j) w v ↔ ∃ u, NStep R i w u ∧ NStep R j u v := by
  induction i generalizing w with
  | zero => simp
  | succ i IH =>
      rw [Nat.succ_add]
      simp only [NStep_succ]
      constructor
      · rintro ⟨u, hwu, h⟩
        obtain ⟨x, hux, hxv⟩ := (IH u).mp h
        exact ⟨x, ⟨u, hwu, hux⟩, hxv⟩
      · rintro ⟨x, ⟨u, hwu, hux⟩, hxv⟩
        exact ⟨u, hwu, (IH u).mpr ⟨x, hux, hxv⟩⟩

/-- `L α n`: `n` is a possible execution length of `α`, i.e. `α` can be executed by exactly
`n` atomic steps. A program may admit several such `n`, for example `a ⋓ (a ;' a)` admits
`1` and `2`, and `∗a` admits every `n`. Tests never occur in test-free programs, so they
admit nothing. -/
def L : Program → ℕ → Prop
  | ·_, n => n = 1
  | α ;' β, n => ∃ i j, L α i ∧ L β j ∧ n = i + j
  | α ⋓ β, n => L α n ∨ L β n
  | ∗α, n => ∃ l : List ℕ, (∀ i ∈ l, L α i) ∧ n = l.sum
  | ?'_, _ => False

variable (M : KripkeModel S)

/-- A test-free program `α` with `voc α = {a}` relates `w` to `v` iff, for some possible
execution length `n` of `α`, there is an `a`-path of exactly `n` steps from `w` to `v`.
(For a test this fails: `?'φ` relates `w` to itself iff `φ` holds at `w`.) -/
theorem relate_iff : ∀ (α : Program), α.testFree → α.voc ⊆ {Sum.inr 0} → ∀ (w v : S),
    relate M α w v ↔ ∃ n, L α n ∧ NStep (M.Rel 0) n w v
  | ?'_, hα, _, _, _ => by simp only [Program.testFree] at hα
  | ·c, _, hv, w, v => by
      obtain rfl : c = 0 := by simpa using hv
      simp only [relate, L]
      constructor
      · intro h; exact ⟨1, rfl, v, h, rfl⟩
      · rintro ⟨n, rfl, u, h, rfl⟩; exact h
  | α ;' β, hαβ, hv, w, v => by
      simp only [Program.testFree] at hαβ
      simp only [Program.voc, Finset.union_subset_iff] at hv
      obtain ⟨hα, hβ⟩ := hαβ
      simp only [relate, L]
      constructor
      · rintro ⟨y, h1, h2⟩
        obtain ⟨i, hi, hwy⟩ := (relate_iff α hα hv.1 w y).mp h1
        obtain ⟨j, hj, hyv⟩ := (relate_iff β hβ hv.2 y v).mp h2
        exact ⟨i + j, ⟨i, j, hi, hj, rfl⟩, (NStep_add i j w v).mpr ⟨y, hwy, hyv⟩⟩
      · rintro ⟨n, ⟨i, j, hi, hj, rfl⟩, h⟩
        obtain ⟨y, hwy, hyv⟩ := (NStep_add i j w v).mp h
        exact ⟨y, (relate_iff α hα hv.1 w y).mpr ⟨i, hi, hwy⟩,
          (relate_iff β hβ hv.2 y v).mpr ⟨j, hj, hyv⟩⟩
  | α ⋓ β, hαβ, hv, w, v => by
      simp only [Program.testFree] at hαβ
      simp only [Program.voc, Finset.union_subset_iff] at hv
      obtain ⟨hα, hβ⟩ := hαβ
      simp only [relate, L]
      rw [relate_iff α hα hv.1 w v, relate_iff β hβ hv.2 w v]
      constructor
      · rintro (⟨n, h, hn⟩ | ⟨n, h, hn⟩)
        · exact ⟨n, Or.inl h, hn⟩
        · exact ⟨n, Or.inr h, hn⟩
      · rintro ⟨n, h | h, hn⟩
        · exact Or.inl ⟨n, h, hn⟩
        · exact Or.inr ⟨n, h, hn⟩
  | ∗α, hα, hv, w, v => by
      simp only [Program.testFree] at hα
      simp only [Program.voc] at hv
      simp only [relate, L]
      constructor
      · intro h
        induction h with
        | refl => exact ⟨0, ⟨[], by simp, rfl⟩, rfl⟩
        | tail _ hstep IH =>
            obtain ⟨n, ⟨l, hl, rfl⟩, hn⟩ := IH
            obtain ⟨i, hi, hi'⟩ := (relate_iff α hα hv _ _).mp hstep
            refine ⟨l.sum + i, ⟨l ++ [i], ?_, by simp⟩, (NStep_add _ _ _ _).mpr ⟨_, hn, hi'⟩⟩
            intro x hx
            simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hl x hx
            · exact hi
      · rintro ⟨n, ⟨l, hl, rfl⟩, hn⟩
        induction l generalizing w with
        | nil =>
            simp only [List.sum_nil, NStep_zero] at hn
            subst hn
            exact Relation.ReflTransGen.refl
        | cons i l IH =>
            rw [List.sum_cons, NStep_add] at hn
            obtain ⟨u, hwu, huv⟩ := hn
            refine Relation.ReflTransGen.head ?_
              (IH u (fun x hx => hl x (List.mem_cons_of_mem _ hx)) huv)
            exact (relate_iff α hα hv w u).mpr ⟨i, hl i (List.mem_cons_self ..), hwu⟩

/-- For a test-free program `α` with `voc α = {a}`, the formula `[α]φ` holds at `w` iff `φ`
holds at all states reachable from `w` by an `a`-path of exactly `n` steps, for all possible
execution lengths `n` of `α`. -/
theorem box_iff (α : Program) (hα : α.testFree) (hv : α.voc ⊆ {Sum.inr 0}) (w : S)
    (φ : Formula) :
    evaluate M w (⌈α⌉φ) ↔ ∀ n, L α n → ∀ v, NStep (M.Rel 0) n w v → evaluate M v φ := by
  simp only [evaluate]
  constructor
  · intro h n hn v hnv; exact h v ((relate_iff M α hα hv w v).mpr ⟨n, hn, hnv⟩)
  · intro h v hwv
    obtain ⟨n, hn, hnv⟩ := (relate_iff M α hα hv w v).mp hwv
    exact h n hn v hnv

end Paths
