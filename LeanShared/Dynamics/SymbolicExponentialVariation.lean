module

public import LeanShared.Dynamics.BilateralShadowingCoding
public import LeanShared.Analysis.GeometricBlockRefinement

/-! Exponential variations of bilateral finite-graph potentials, expressed
directly through agreement of finite words.  Bounds on block radii yield
the ordinary every-radius condition used in symbolic transfer theory.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
variable {A : Type*} {R : A → A → Prop}

@[expose] def WindowAgreement (a b : Path R) (radius : ℕ) : Prop :=
  ∀ k : ℤ, -(radius : ℤ) ≤ k → k ≤ radius → a.val k = b.val k

@[expose] def HasExponentialVariations (φ : Path R → ℝ) : Prop :=
  ∃ rate > 0, rate < 1 ∧ ∃ C ≥ 0,
    ∀ radius : ℕ, ∀ a b : Path R, WindowAgreement a b radius → |φ b - φ a| ≤ C * rate ^ radius

theorem hasExponentialVariations_of_block (φ : Path R → ℝ) (block : ℕ) (positiveBlock : 0 < block)
    (θ C : ℝ) (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeC : 0 ≤ C)
    (bound : ∀ n : ℕ, ∀ a b : Path R, WindowAgreement a b (block * n) → |φ b - φ a| ≤ C * θ ^ n) :
    HasExponentialVariations φ := by
  have restriction (m n : ℕ) (smaller : m ≤ n) (a b : Path R)
      (agreement : WindowAgreement a b n) : WindowAgreement a b m := by
    intro k lower upper
    exact agreement k (by omega) (by omega)
  obtain ⟨rate, positiveRate, smallRate, D, nonnegativeD, uniform⟩ :=
    GeometricBlockRefinement.exists_bound φ (fun n a b => WindowAgreement a b n) restriction
      block positiveBlock θ C positiveθ smallθ nonnegativeC
      (fun n a b same => by simpa only [Real.norm_eq_abs] using bound n a b same)
  refine ⟨rate, positiveRate, smallRate, D, nonnegativeD, ?_⟩
  intro n a b same
  simpa only [Real.norm_eq_abs] using uniform n a b same

end LeanShared.BilateralShadowingCoding
