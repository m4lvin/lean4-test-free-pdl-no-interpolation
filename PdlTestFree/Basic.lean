module

public import Pdl.Semantics
public import Pdl.Vocab

@[expose] public section

/-! # Basics

The definitions from Section 3 of the paper that are not already in `lean4-pdl`:
test-free formulas and programs, modal depth, depth-bounded agreement of two states,
and interpolants. -/

/-! ## Test-free formulas and programs -/

mutual
  /-- A formula is test-free if no test occurs in it. -/
  @[simp]
  def Formula.testFree : Formula → Prop
    | ⊥ => True
    | ·_ => True
    | ~φ => φ.testFree
    | φ ⋀ ψ => φ.testFree ∧ ψ.testFree
    | ⌈α⌉ φ => α.testFree ∧ φ.testFree
  /-- A program is test-free if no test occurs in it. -/
  @[simp]
  def Program.testFree : Program → Prop
    | ·_ => True
    | α ;' β => α.testFree ∧ β.testFree
    | α ⋓ β => α.testFree ∧ β.testFree
    | ∗α => α.testFree
    | ?'_ => False
end

/-- The vocabulary of a test-free program consists of atomic programs only. -/
theorem Program.testFree_voc : ∀ (α : Program), α.testFree → ∀ x ∈ α.voc, ∃ c, x = Sum.inr c
  | ·c, _, x, hx => ⟨c, by simpa using hx⟩
  | α ;' β, h, x, hx => by
      simp only [Program.testFree] at h
      simp only [Program.voc, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact Program.testFree_voc α h.1 x hx
      · exact Program.testFree_voc β h.2 x hx
  | α ⋓ β, h, x, hx => by
      simp only [Program.testFree] at h
      simp only [Program.voc, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact Program.testFree_voc α h.1 x hx
      · exact Program.testFree_voc β h.2 x hx
  | ∗α, h, x, hx => Program.testFree_voc α h x hx
  | ?'_, h, _, _ => by simp only [Program.testFree] at h

/-! ## Modal depth and depth-bounded agreement -/

/-- The modal depth of a (test-free) formula. It is shallow in the sense that it does not
care about the structure of programs: `⟨a ⋓ b⟩p` and `⟨a ;' (∗b ⋓ c)⟩p` both have depth `1`. -/
def mdepth : Formula → ℕ
  | ⊥ => 0
  | ·_ => 0
  | ~φ => mdepth φ
  | φ ⋀ ψ => max (mdepth φ) (mdepth ψ)
  | ⌈_⌉ φ => mdepth φ + 1

/-- `agree M A j w₁ w₂`: the states `w₁` and `w₂` agree test-free on `A` up to `j`, i.e. they
satisfy the same test-free formulas with vocabulary in `A` and modal depth at most `j`. -/
def agree {W : Type} (M : KripkeModel W) (A : Vocab) (j : ℕ) (w₁ w₂ : W) : Prop :=
  ∀ φ : Formula, φ.testFree → φ.voc ⊆ A → mdepth φ ≤ j →
    (evaluate M w₁ φ ↔ evaluate M w₂ φ)
