module

public import LeanShared.Dynamics.HyperbolicReferenceJacobianHolder
public import LeanShared.Dynamics.HyperbolicReferenceCoboundary
public import LeanShared.Geometry.BoundedRiemannianFractionalHolder
public import LeanShared.Geometry.RegularCoreHolderExtension
public import LeanShared.Geometry.BoundedRiemannianDiameter
public import LeanShared.Analysis.CompactLogHolder
import Mathlib.Tactic.Ring

/-! The actual potential formed with the supplied continuous metric is
cohomologous on the basic set to a genuinely constructed global fractional
potential. The reference immersion, unstable Hölder regularity, extension
and metric-volume coboundary are all derived. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold FractionalManifoldRegularity
open scoped Topology Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_regular_potential_representative (b : BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (g : M → ℝ) (weightRegular : Regular (E := E) (F := ℝ) q g)
    (weightPositive : ∀ x ∈ Λ, 0 < g x) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ ψ : M → ℝ,
      Regular (E := E) (F := ℝ) α ψ ∧ ∃ u : M → ℝ, Continuous u ∧
        ∀ x ∈ Λ, b.hyperbolic.potential g x = ψ x + u x - u (T x) := by
  let h := b.hyperbolic
  let d := CanonicalSmoothReferenceMetric.canonicalData (E := E) (M := M)
  obtain ⟨β, positiveβ, smallβ, HJ, nonnegativeHJ, jacobianHolder⟩ :=
    h.exists_reference_log_jacobian_holder regularity forwardRegular inverseRegular d.map d.smooth d.injective
  let a := min (q / 2) (1 / 2)
  have positiveA : 0 < a := lt_min (by linarith) (by norm_num)
  have smallA : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have lowerA : a < q := by have := min_le_left (q / 2) (1 / 2); dsimp only [a]; linarith
  obtain ⟨HG, nonnegativeHG, weightHolder⟩ :=
    BoundedRiemannianMetric.real_fractional_exists_holder g positiveA smallA lowerA weightRegular
  have forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T := forwardRegular.mdifferentiable regularity.le
  have inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm := inverseRegular.mdifferentiable regularity.le
  obtain ⟨u, continuousU, coboundary⟩ := h.exists_canonical_reference_coboundary forward inverse g
  let J : M → ℝ := fun x => Real.log (h.referenceUnstableJacobian d.map x)
  let φ : M → ℝ := fun x => Real.log (g x) - J x
  have compactCore : IsCompact Λ := h.compact
  have extension : ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ ψ : M → ℝ,
      Regular (E := E) (F := ℝ) α ψ ∧ EqOn φ ψ Λ := by
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    obtain ⟨HL, nonnegativeHL, logHolder⟩ := CompactLogHolder.bound compactCore g a HG positiveA smallA.le
      nonnegativeHG (fun x hx => (weightPositive x hx).ne')
      (fun x _ y _ => weightHolder x y)
    let α := min β a
    have positiveα : 0 < α := lt_min positiveβ positiveA
    have smallα : α < 1 := (min_le_right _ _).trans_lt smallA
    have power (s : ℝ) (lower : α ≤ s) (x y : M) : dist x y ^ s ≤ dist x y ^ α :=
      Real.rpow_le_rpow_of_exponent_ge' dist_nonneg (BoundedRiemannianMetric.dist_le_one x y) positiveα.le lower
    have bound (x : M) (hx : x ∈ Λ) (y : M) (hy : y ∈ Λ) :
        |φ x - φ y| ≤ (HL + HJ) * dist x y ^ α := by
      have first := (logHolder x hx y hy).trans
        (mul_le_mul_of_nonneg_left (power a (min_le_right _ _) x y) nonnegativeHL)
      have other := (jacobianHolder x hx y hy).trans
        (mul_le_mul_of_nonneg_left (power β (min_le_left _ _) x y) nonnegativeHJ)
      have rewriteDifference : φ x - φ y = (Real.log (g x) - Real.log (g y)) - (J x - J y) := by
        dsimp only [φ]
        ring
      rw [rewriteDifference]
      exact (abs_sub _ _).trans ((add_le_add first other).trans_eq (by ring))
    obtain ⟨ψ, regularψ, sameψ⟩ := BoundedRiemannianMetric.exists_regular_core_extension
      Λ φ α (HL + HJ) positiveα smallα (add_nonneg nonnegativeHL nonnegativeHJ) bound
    exact ⟨α, positiveα, smallα, ψ, regularψ, sameψ⟩
  obtain ⟨α, positiveα, smallα, ψ, regularψ, sameψ⟩ := extension
  refine ⟨α, positiveα, smallα, ψ, regularψ, u, continuousU, fun x hx => ?_⟩
  rw [← sameψ hx]
  exact coboundary x hx

end LeanShared.HyperbolicBasicSet
