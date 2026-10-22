module

public import LeanShared.Geometry.SupportedPairingNontrivial

/-! The ordinary smooth-test distribution identity determines the common
embedding into the regular dual. Compatibility on completed test functions
and nontriviality are consequences, not extra spectral source fields. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology BoundedContinuousFunction
namespace LeanShared.SmoothSupportedManifoldCore

variable {E M Reg B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  {V K : Set M} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem common_identity_of_smooth_tests
    (σ : Measure K) [IsFiniteMeasure σ]
    (q : core (E := E) V →ₗ[ℂ] Reg) (hdense : DenseRange q)
    (physical : Reg →L[ℂ] (K →ᵇ ℂ))
    (hphysical : ∀ c, physical (q c) = physicalCore V K c)
    (qa : core (E := E) V →ₗ[ℂ] B) (a : B →L[ℂ] (Reg →L[ℂ] ℂ))
    (htest : ∀ c d, a (qa c) (q d) =
      ∫ x : K, functions V c x.val * functions V d x.val ∂σ) (c : core (E := E) V) :
    a (qa c) = SupportedRegularPairing.embedding σ physical (physicalCore V K c) := by
  apply ContinuousLinearMap.ext
  intro v
  apply hdense.induction_on
    (p := fun v => a (qa c) v =
      SupportedRegularPairing.embedding σ physical (physicalCore V K c) v) v
    (isClosed_eq (a (qa c)).continuous
      (SupportedRegularPairing.embedding σ physical (physicalCore V K c)).continuous)
  intro d
  rw [SupportedRegularPairing.embedding_apply, hphysical, htest]
  rfl

end LeanShared.SmoothSupportedManifoldCore
