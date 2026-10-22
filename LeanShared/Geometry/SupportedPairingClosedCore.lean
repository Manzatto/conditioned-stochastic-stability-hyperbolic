module

public import LeanShared.Geometry.SupportedRegularPairing
public import LeanShared.Geometry.SupportedCoreConjugation
public import LeanShared.Analysis.DyadicCompletion

/-! # The faithful common ambient space is the actual closed supported core

The regular realization need not be dense in all continuous functions on K.
Its closed range is a genuine Banach space; integration is faithful there
using reference positivity only on the live collar. Cutoff outputs belong to
this space by supported smooth approximation, with no C0-to-Cu smoothing.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction Manifold ContDiff
namespace LeanShared.SupportedPairingClosedCore

variable {X Reg : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]

abbrev space (physical : Reg →L[ℂ] (X →ᵇ ℂ)) :=
  DyadicCompletion.closedCore physical.toLinearMap

def regularMap (physical : Reg →L[ℂ] (X →ᵇ ℂ)) : Reg →L[ℂ] space physical :=
  physical.codRestrict (space physical)
    (fun v => physical.toLinearMap.range.le_topologicalClosure ⟨v, rfl⟩)

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem regularMap_coe (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (v : Reg) :
    (regularMap physical v : X →ᵇ ℂ) = physical v := rfl

omit [MeasurableSpace X] [BorelSpace X] in
theorem regularMap_dense (physical : Reg →L[ℂ] (X →ᵇ ℂ)) : DenseRange (regularMap physical) :=
  DyadicCompletion.coreLift_dense physical.toLinearMap

def pairing (σ : Measure X) [IsFiniteMeasure σ]
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) : space physical →L[ℂ] (Reg →L[ℂ] ℂ) :=
  (SupportedRegularPairing.embedding σ physical).comp (space physical).subtypeL

@[simp] theorem pairing_apply (σ : Measure X) [IsFiniteMeasure σ]
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (f : space physical) (v : Reg) :
    pairing σ physical f v = ∫ x, f.val x * physical v x ∂σ := rfl

omit [MeasurableSpace X] [BorelSpace X] in
theorem star_mem_space_of_regular_conjugation
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (conjugateReg : Reg → Reg)
    (hconj : ∀ v, physical (conjugateReg v) = star (physical v))
    (f : space physical) : star (f : X →ᵇ ℂ) ∈ space physical := by
  apply map_mem_closure continuous_star f.property
  rintro _ ⟨v, rfl⟩
  exact ⟨conjugateReg v, hconj v⟩

/-- Faithfulness on the actual closed core needs no reference support on
null dangling pieces of the closed live boundary. -/
theorem pairing_injective_of_star_and_zero
    (σ : Measure X) [IsFiniteMeasure σ]
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (O : Set X) (hO : O ⊆ σ.support)
    (hstar : ∀ f : space physical, star (f : X →ᵇ ℂ) ∈ space physical)
    (hzero : ∀ f : space physical, ∀ x ∉ O, f.val x = 0) :
    Function.Injective (pairing σ physical) := by
  have hfaithful : ∀ f : space physical, pairing σ physical f = 0 → f = 0 := by
    intro f hf
    let f0 : X →ᵇ ℂ := f.val
    let J := (SupportedRegularPairing.integralFunctional σ).comp
      (ContinuousLinearMap.mul ℂ (X →ᵇ ℂ) f0)
    have hJ : J (star f0) = 0 := by
      apply closure_minimal ?_ (isClosed_eq J.continuous continuous_const) (hstar f)
      rintro _ ⟨v, rfl⟩
      exact congrArg (fun z : Reg →L[ℂ] ℂ => z v) hf
    have hInt : ∫ x, ‖f0 x‖ ^ 2 ∂σ = 0 := by
      have he : ∀ x, ‖f0 x‖ ^ 2 = (f0 x * star (f0 x)).re := by
        intro x
        change ‖f0 x‖ ^ 2 = (f0 x * (starRingEnd ℂ) (f0 x)).re
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        norm_cast
      simp_rw [he]
      have hr := integral_re ((f0 * star f0).integrable σ)
      change (∫ x, (f0 x * star (f0 x)).re ∂σ) = (∫ x, f0 x * star (f0 x) ∂σ).re at hr
      exact hr.trans (congrArg Complex.re hJ)
    have hi : Integrable (fun x => ‖f0 x‖ ^ 2) σ := by
      have hp := ((f0 * star f0).integrable σ).re
      convert hp using 1
      funext x
      change ‖f0 x‖ ^ 2 = (f0 x * (starRingEnd ℂ) (f0 x)).re
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
    have hae : ∀ᵐ x ∂σ, f0 x = 0 := by
      filter_upwards [(integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f0 x‖) hi).mp hInt] with x hx
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
    have hs : σ.support ⊆ {x | f0 x = 0} :=
      σ.support_subset_of_isClosed (isClosed_eq f0.continuous continuous_const) hae
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    by_cases hx : x ∈ O
    · exact hs (hO hx)
    · exact hzero f x hx
  intro f g hfg
  apply sub_eq_zero.mp
  exact hfaithful (f - g) (by rw [map_sub, hfg, sub_self])

end LeanShared.SupportedPairingClosedCore

namespace LeanShared.SmoothSupportedManifoldCore
open SupportedPairingClosedCore
variable {E M Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {V K : Set M} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (q : core (E := E) V →ₗ[ℂ] Reg) (dense : DenseRange q)
  (physical : Reg →L[ℂ] (K →ᵇ ℂ))
  (hphysical : ∀ c, physical (q c) = physicalCore V K c)

include dense hphysical in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [MeasurableSpace K] [BorelSpace K] in
theorem physical_closedCore_eq_smooth_closure :
    (space physical : Set (K →ᵇ ℂ)) = closure (range (physicalCore (E := E) V K)) := by
  apply Subset.antisymm
  · apply closure_minimal ?_ isClosed_closure
    rintro _ ⟨v, rfl⟩
    apply map_mem_closure physical.continuous (dense v)
    rintro _ ⟨c, rfl⟩
    exact ⟨c, (hphysical c).symm⟩
  · apply closure_mono
    rintro _ ⟨c, rfl⟩
    exact ⟨q c, hphysical c⟩

include dense hphysical in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [MeasurableSpace K] [BorelSpace K] in
theorem physical_closedCore_star (f : space physical) : star (f : K →ᵇ ℂ) ∈ space physical := by
  change star (f : K →ᵇ ℂ) ∈ (space physical : Set (K →ᵇ ℂ))
  rw [physical_closedCore_eq_smooth_closure q dense physical hphysical]
  apply map_mem_closure continuous_star
    ((physical_closedCore_eq_smooth_closure q dense physical hphysical).subset f.property)
  rintro _ ⟨c, rfl⟩
  refine ⟨conjugate V c, ?_⟩
  apply BoundedContinuousFunction.ext
  intro x
  rfl

include dense hphysical in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [MeasurableSpace K] [BorelSpace K] in
theorem physical_closedCore_zero_outside (f : space physical) (x : K) (hx : x.val ∉ V) :
    f.val x = 0 := by
  have hf := (physical_closedCore_eq_smooth_closure q dense physical hphysical).subset f.property
  apply closure_minimal ?_ (isClosed_eq (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) x).continuous continuous_const) hf
  rintro _ ⟨c, rfl⟩
  exact zero_outside V c x.val hx

include dense hphysical in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] in
theorem physical_closedCore_pairing_injective
    (σ : Measure K) [IsFiniteMeasure σ]
    (hpositive : {x : K | x.val ∈ V} ⊆ σ.support) :
    Function.Injective (SupportedPairingClosedCore.pairing σ physical) := by
  exact pairing_injective_of_star_and_zero σ physical {x : K | x.val ∈ V} hpositive
    (physical_closedCore_star q dense physical hphysical)
    (fun f x hx => physical_closedCore_zero_outside q dense physical hphysical f x hx)

include hphysical in
omit [MeasurableSpace K] [BorelSpace K] in
theorem mem_physical_closedCore_of_tsupport (hK : IsClosed K) (hV : IsOpen V)
    (f : K →ᵇ ℂ) (hf : tsupport f ⊆ {x : K | x.val ∈ V}) : f ∈ space physical := by
  apply closure_mono ?_ (physicalCore_supported_dense (E := E) hK hV f hf)
  rintro _ ⟨c, rfl⟩
  exact ⟨q c, hphysical c⟩

include hphysical in
omit [MeasurableSpace K] [BorelSpace K] in
theorem cutoff_range_subset_physical_closedCore (hK : IsClosed K) (hV : IsOpen V)
    (Q : (K →ᵇ ℂ) →L[ℂ] (K →ᵇ ℂ))
    (hQ : ∀ f, tsupport (Q f) ⊆ {x : K | x.val ∈ V}) :
    ∀ f, Q f ∈ space physical :=
  fun f => mem_physical_closedCore_of_tsupport q physical hphysical hK hV (Q f) (hQ f)

end LeanShared.SmoothSupportedManifoldCore
