module

public import LeanShared.Geometry.SupportedSmoothDensity
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-! The continuous-function embedding into the dual of the actual regular
test space is constructed by integration. Faithfulness is proved on the live
region using support-qualified smooth approximation and reference positivity. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace LeanShared.SupportedRegularPairing

variable {X Reg : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]

def integralFunctional (σ : Measure X) [IsFiniteMeasure σ] : (X →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous {
    toFun := fun f => ∫ x, f x ∂σ
    map_add' := fun f g => integral_add (f.integrable σ) (g.integrable σ)
    map_smul' := fun c f => by
      simp only [BoundedContinuousFunction.smul_apply, integral_smul, RingHom.id_apply] }
    (σ.real univ) (fun f => by
      change ‖∫ x, f x ∂σ‖ ≤ σ.real univ * ‖f‖
      have h := norm_integral_le_of_norm_le_const (μ := σ) (f := fun x => f x)
        (C := ‖f‖) (Filter.Eventually.of_forall f.norm_coe_le_norm)
      simpa only [mul_comm] using h)

/-- The literal bilinear distribution pairing against regular test functions. -/
def embedding (σ : Measure X) [IsFiniteMeasure σ]
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) : (X →ᵇ ℂ) →L[ℂ] (Reg →L[ℂ] ℂ) :=
  LinearMap.mkContinuous {
    toFun := fun f => (integralFunctional σ).comp ((ContinuousLinearMap.mul ℂ (X →ᵇ ℂ) f).comp physical)
    map_add' := fun f g => by
      ext v
      change integralFunctional σ ((f + g) * physical v) =
        integralFunctional σ (f * physical v) + integralFunctional σ (g * physical v)
      simp only [add_mul, map_add]
    map_smul' := fun c f => by
      ext v
      change integralFunctional σ ((c • f) * physical v) = c • integralFunctional σ (f * physical v)
      simp only [smul_mul_assoc, map_smul] }
    (‖integralFunctional σ‖ * ‖physical‖) (fun f => by
      calc
        ‖(integralFunctional σ).comp ((ContinuousLinearMap.mul ℂ (X →ᵇ ℂ) f).comp physical)‖
          ≤ ‖integralFunctional σ‖ * (‖ContinuousLinearMap.mul ℂ (X →ᵇ ℂ) f‖ * ‖physical‖) :=
            (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
        _ ≤ ‖integralFunctional σ‖ * (‖f‖ * ‖physical‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℂ _ f) (norm_nonneg _)) (norm_nonneg _)
        _ = (‖integralFunctional σ‖ * ‖physical‖) * ‖f‖ := by ring)

@[simp] theorem embedding_apply (σ : Measure X) [IsFiniteMeasure σ]
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (f : X →ᵇ ℂ) (v : Reg) :
    embedding σ physical f v = ∫ x, f x * physical v x ∂σ := rfl

/-- Only functions whose support meets the reference support faithfully are
claimed faithful; dangling null pieces of a closed live boundary are allowed. -/
theorem faithful_of_supported_approximation
    (σ : Measure X) [IsFiniteMeasure σ]
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (O : Set X)
    (hO : O ⊆ σ.support)
    (happrox : ∀ f : X →ᵇ ℂ, tsupport f ⊆ O → f ∈ closure (range physical))
    (f : X →ᵇ ℂ) (hf : tsupport f ⊆ O) (hzero : embedding σ physical f = 0) : f = 0 := by
  let J := (integralFunctional σ).comp (ContinuousLinearMap.mul ℂ (X →ᵇ ℂ) f)
  have hJ : J (star f) = 0 := by
    have hd : star f ∈ closure (range physical) := happrox _ (by
      apply (closure_mono ?_).trans hf
      intro x hx
      exact fun hz => hx (by change star (f x) = 0; simp [hz]))
    apply closure_minimal ?_ (isClosed_eq J.continuous continuous_const) hd
    rintro _ ⟨v, rfl⟩
    exact congrArg (fun z : Reg →L[ℂ] ℂ => z v) hzero
  have hInt : ∫ x, ‖f x‖ ^ 2 ∂σ = 0 := by
    have he : ∀ x, ‖f x‖ ^ 2 = (f x * star (f x)).re := by
      intro x
      change ‖f x‖ ^ 2 = (f x * (starRingEnd ℂ) (f x)).re
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
    simp_rw [he]
    have hr := integral_re ((f * star f).integrable σ)
    change (∫ x, (f x * star (f x)).re ∂σ) = (∫ x, f x * star (f x) ∂σ).re at hr
    exact hr.trans (congrArg Complex.re hJ)
  have hi : Integrable (fun x => ‖f x‖ ^ 2) σ := by
    have hp := ((f * star f).integrable σ).re
    convert hp using 1
    funext x
    change ‖f x‖ ^ 2 = (f x * (starRingEnd ℂ) (f x)).re
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  have hae : ∀ᵐ x ∂σ, f x = 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖) hi).mp hInt] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hs : σ.support ⊆ {x | f x = 0} :=
    σ.support_subset_of_isClosed (isClosed_eq f.continuous continuous_const) hae
  ext x
  by_contra hx
  exact hx (hs (hO (hf (subset_tsupport f hx))))

end LeanShared.SupportedRegularPairing

open scoped Manifold ContDiff
namespace LeanShared.SmoothSupportedManifoldCore

variable {E M Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {V K : Set M} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- The constructed distribution embedding is faithful on the actual open
live collar. Reference support is needed only there, not on the whole K. -/
theorem physical_pairing_faithful (hK : IsClosed K) (hV : IsOpen V)
    (σ : Measure K) [IsFiniteMeasure σ]
    (q : core (E := E) V →ₗ[ℂ] Reg)
    (physical : Reg →L[ℂ] (K →ᵇ ℂ))
    (hphysical : ∀ c, physical (q c) = physicalCore V K c)
    (hpositive : {x : K | x.val ∈ V} ⊆ σ.support)
    (f : K →ᵇ ℂ) (hf : tsupport f ⊆ {x : K | x.val ∈ V})
    (hzero : SupportedRegularPairing.embedding σ physical f = 0) : f = 0 := by
  apply SupportedRegularPairing.faithful_of_supported_approximation
    σ physical {x : K | x.val ∈ V} hpositive ?_ f hf hzero
  intro g hg
  apply closure_mono ?_ (physicalCore_supported_dense (E := E) hK hV g hg)
  rintro _ ⟨c, rfl⟩
  exact ⟨q c, hphysical c⟩

end LeanShared.SmoothSupportedManifoldCore
