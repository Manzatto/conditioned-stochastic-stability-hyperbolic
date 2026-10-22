module
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! A genuine native tangent derivative bound controls Riemannian length
distance. This does not identify that distance with an arbitrary compatible
metric on the underlying manifold. -/
public noncomputable section
namespace LeanShared.RiemannianDerivativeDistanceBound
open Set MeasureTheory Measure Bundle IsManifold Manifold
open scoped Topology Manifold ContDiff Bundle ENNReal

theorem riemannianEDist_le
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [RiemannianBundle (fun x : N => TangentSpace (𝓘(ℝ,F)) x)]
    (f : M → N) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f)
    (C : ℝ) (positive : 0 < C)
    (bound : ∀ x, ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x‖ ≤ C) (x y : M) :
    Manifold.riemannianEDist (𝓘(ℝ,F)) (f x) (f y) ≤
      ENNReal.ofReal C * Manifold.riemannianEDist (𝓘(ℝ,E)) x y := by
  have nonzero : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr positive).ne'
  conv_rhs => rw [Manifold.riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne nonzero ENNReal.ofReal_ne_top]
  apply le_iInf
  intro γ
  rw [ENNReal.mul_iInf_of_ne nonzero ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hγ
  let η := γ.map smooth.continuous
  have smoothη : CMDiff 1 η := smooth.comp hγ
  calc
    _ ≤ ∫⁻ t, ‖mfderiv% η t 1‖ₑ := by
      rw [Manifold.riemannianEDist]
      exact biInf_le _ smoothη
    _ ≤ ∫⁻ t, ENNReal.ofReal C * ‖mfderiv% γ t 1‖ₑ := by
      apply lintegral_mono
      intro t
      have derivative := mfderiv_comp t (smooth.mdifferentiable (by norm_num) (γ t))
        (hγ.mdifferentiable (by norm_num) t)
      change ‖mfderiv% (f ∘ γ) t 1‖ₑ ≤ _
      rw [derivative,ContinuousLinearMap.comp_apply]
      have estimate := ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (γ t)).le_opNorm (mfderiv% γ t 1)).trans
        (mul_le_mul_of_nonneg_right (bound (γ t)) (norm_nonneg _))
      simpa only [ENNReal.ofReal_mul positive.le,ofReal_norm] using
        ENNReal.ofReal_le_ofReal estimate
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end LeanShared.RiemannianDerivativeDistanceBound
