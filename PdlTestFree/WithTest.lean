module

public import PdlTestFree.NoInterpolation

@[expose] public section

open TestfreeNoItp

/-! # With a test there is an interpolant

If we allow test operators, then there is an interpolant for `⋀Γ₁ → ¬⋀Γ₂`. -/

/-- The formula `[(p?;a)*](p → ⟨a⟩⊤)` which uses a test.
This formulas says that along every `p`-path, every `p`-state has a successor. -/
def testIP : Formula := ⌈∗((?'p) ;' a)⌉(p ↣ Formula.neg (⌈a⌉⊥))

/-- The formula `testIP` is not test-free.. -/
lemma not_testFree_withTest : ¬ testIP.testFree := by
  simp [testIP]

/-! ## Γ₁ implies `testIP` -/

/-- `Γ₁ ⊨ [(p?;a)*](p → ⟨a⟩⊤)`. -/
lemma gammaOne_withTest {W : Type} (M : KripkeModel W) (w : W)
    (h1 : ∀ φ ∈ gammaOne, evaluate M w φ) : evaluate M w testIP := by
  obtain ⟨hs, hbody⟩ := (gammaOne_iff M w).mp h1
  simp only [testIP, evaluate, relate, not_and, not_not]
  intro v hv
  -- every state reached along `(p?;a)*` from `w` is `a*`-reachable and satisfies `s`
  have key : Relation.ReflTransGen (M.Rel 0) w v ∧ M.val v 2 := by
    induction hv with
    | refl => exact ⟨.refl, hs⟩
    | tail _ hvu IH =>
        obtain ⟨y, ⟨rfl, hpv⟩, hvu⟩ := hvu
        exact ⟨IH.1.tail hvu, (hbody _ IH.1 hpv IH.2).2 _ hvu⟩
  intro hpv hdead
  obtain ⟨u, hu⟩ := (hbody v key.1 hpv key.2).1
  exact hdead u hu

/-! ## Γ₂ implies the negation of `testIP` -/

/-- `Γ₂ ⊨ ¬[(p?;a)*](p → ⟨a⟩⊤)`. -/
lemma gammaTwo_not_withTest {W : Type} (M : KripkeModel W) (w : W)
    (h2 : ∀ φ ∈ gammaTwo, evaluate M w φ) : ¬ evaluate M w testIP := by
  obtain ⟨hqp, -, v, hv, hqv, hdead⟩ := (gammaTwo_iff M w).mp h2
  simp only [testIP, evaluate, relate, not_forall, not_and, not_not, not_exists, exists_prop,
    not_false_eq_true, and_true]
  refine ⟨v, ?_, hqp v hv hqv, hdead⟩
  -- the path to `v` consists of `p`-states, hence is a `(p?;a)*`-path
  exact Relation.ReflTransGen.mono (fun x y ⟨hxy, hpx, _⟩ => ⟨x, ⟨rfl, hpx⟩, hxy⟩) _ _
    (gammaTwo_path h2 hv hqv)

/-! ## `testIP` is an interpolant for Γ₁;Γ₂ -/

/-- `[(p?;a)*](p → ⟨a⟩⊤)` is an `Interpolant` for `⋀Γ₁ → ¬⋀Γ₂` (with a test). -/
theorem withTest_Interpolant :
    Interpolant (con gammaOne) (~ con gammaTwo) testIP := by
  refine ⟨?_, ?_, ?_⟩
  · rw [voc_gammaOne_gammaTwo]
    decide
  · intro W M w
    simp only [evaluate, conEval, not_and, not_not]
    exact gammaOne_withTest M w
  · intro W M w
    simp only [evaluate, conEval, not_and, not_not]
    exact fun hθ h2 => gammaTwo_not_withTest M w h2 hθ
