module
public import LeanShared.MeasureTheory.IntrinsicCoordinatePatchMeasures
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.Calculus.ContDiff.Comp

public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LeanShared.ImmersionPullbackJacobian
variable {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem chain {γ : U → E} {F : E → E} {x : U}
    {Dγ : U →L[ℝ] E} {DF : E →L[ℝ] E}
    (hγ : HasFDerivAt γ Dγ x) (hF : HasFDerivAt F DF (γ x)) :
    (fderiv ℝ (F ∘ γ) x).toLinearMap.normDet =
      (DF.toLinearMap.domRestrict Dγ.toLinearMap.range).normDet *
        Dγ.toLinearMap.normDet := by
  rw [(hF.comp x hγ).fderiv]
  exact LinearMap.normDet_comp Dγ.toLinearMap DF.toLinearMap

omit [FiniteDimensional ℝ E] in
/-- The actual rectangular Jacobian, including its zero extension off the
parameter domain. -/
theorem density_chain {γ : U → E} {F : E → E} {s : Set U}
    (hγ : DifferentiableOn ℝ γ s) (hs : IsOpen s)
    (hF : ∀ x ∈ s, DifferentiableAt ℝ F (γ x)) (x : U) (hx : x ∈ s) :
    IntrinsicCoordinatePatchMeasures.density (F ∘ γ) s x =
      ENNReal.ofReal (((fderiv ℝ F (γ x)).toLinearMap.domRestrict
        (fderiv ℝ γ x).toLinearMap.range).normDet) *
      IntrinsicCoordinatePatchMeasures.density γ s x := by
  simp only [IntrinsicCoordinatePatchMeasures.density, Set.indicator_of_mem hx]
  rw [chain ((hγ x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt
    (hF x hx).hasFDerivAt, ENNReal.ofReal_mul (LinearMap.normDet_nonneg _)]

omit [FiniteDimensional ℝ E] in
/-- A pointwise weight bound by the actual tangent Jacobian gives the
parametrized weighted pullback estimate with structural constant one. -/
theorem weighted_pullback [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure U)
    {γ : U → E} {F : E → E} {s : Set U} {t : Set E}
    (hs : IsOpen s) (ht : IsOpen t)
    (hγ : ContDiffOn ℝ 1 γ s) (hF : ContDiffOn ℝ 1 F t)
    (image : Set.MapsTo γ s t) (mγ : Measurable γ) (mF : Measurable F)
    (a f : E → ℝ≥0∞) (ma : Measurable a) (mf : Measurable f)
    (C : ℝ≥0∞)
    (cost : ∀ x ∈ s, a (γ x) ≤ C * ENNReal.ofReal
      (((fderiv ℝ F (γ x)).toLinearMap.domRestrict
        (fderiv ℝ γ x).toLinearMap.range).normDet)) :
    ∫⁻ z, a z * f (F z) ∂((μ.withDensity
      (IntrinsicCoordinatePatchMeasures.density γ s)).map γ) ≤
      C * ∫⁻ z, f z ∂((μ.withDensity
        (IntrinsicCoordinatePatchMeasures.density (F ∘ γ) s)).map (F ∘ γ)) := by
  have comp : ContDiffOn ℝ 1 (F ∘ γ) s := hF.comp hγ image
  rw [lintegral_map (f := fun z => a z * f (F z)) (ma.mul (mf.comp mF)) mγ,
    lintegral_map mf (mF.comp mγ),
    lintegral_withDensity_eq_lintegral_mul μ
      (IntrinsicCoordinatePatchMeasures.measurable_density hγ hs)
      (g := fun x => a (γ x) * f (F (γ x)))
      ((ma.mul (mf.comp mF)).comp mγ),
    lintegral_withDensity_eq_lintegral_mul μ
      (IntrinsicCoordinatePatchMeasures.measurable_density comp hs)
      (g := fun x => f ((F ∘ γ) x)) (mf.comp (mF.comp mγ))]
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [← lintegral_const_mul (μ := μ) C
    (f := fun x => IntrinsicCoordinatePatchMeasures.density (F ∘ γ) s x * f (F (γ x)))
    ((IntrinsicCoordinatePatchMeasures.measurable_density comp hs).mul
      (mf.comp (mF.comp mγ)))]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ s
  · have chainEq := density_chain (hγ.differentiableOn one_ne_zero) hs
      (fun y hy => ((hF.differentiableOn one_ne_zero) (γ y) (image hy)).differentiableAt
        (ht.mem_nhds (image hy))) x hx
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [chainEq]
    calc
      _ ≤ IntrinsicCoordinatePatchMeasures.density γ s x *
          ((C * ENNReal.ofReal (((fderiv ℝ F (γ x)).toLinearMap.domRestrict
            (fderiv ℝ γ x).toLinearMap.range).normDet)) * f (F (γ x))) :=
        mul_le_mul le_rfl (mul_le_mul (cost x hx) le_rfl bot_le bot_le)
          bot_le bot_le
      _ = _ := by ring
  · simp [IntrinsicCoordinatePatchMeasures.density, hx]

end LeanShared.ImmersionPullbackJacobian
