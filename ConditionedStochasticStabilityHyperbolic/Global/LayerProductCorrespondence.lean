module

public import ConditionedStochasticStabilityHyperbolic.Global.LayerQuasiErgodic

/-!
# Exact dominant-layer product correspondence

The global leading eigenfunction restricts to the dominant diagonal's
leading eigenfunction. The assembled functional and pointwise eigenfunction
therefore give the same product pairing on every global continuous test
function. This identifies the global limiting product with the local one,
instead of assuming support or weak convergence of the global product.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.LayerProductCorrespondence

open LayerOperators ComplexStrongFeller LayerRankOne DominantBlockGap

section RawData

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem transported_mean {P Q : E →L[ℝ] E} {one : E}
    (h : P = Q) (d : RankOneSpectralData P one) : (h ▸ d).mean = d.mean := by
  cases h
  rfl

private theorem transported_vector {P Q : E →L[ℝ] E} {one : E}
    (h : P = Q) (d : RankOneSpectralData P one) : (h ▸ d).eigenvector = d.eigenvector := by
  cases h
  rfl

theorem lower_raw_mean [CompleteSpace E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] F) {D : F →L[ℝ] F} {oneF : F}
    (d : RankOneSpectralData D oneF) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    (ofSubordinateLower A B d hCA hβ hβr hA).mean =
      assembledMean (d.rate⁻¹ • A) (d.rate⁻¹ • B) d := by
  dsimp only [ofSubordinateLower, RankOneSpectralData.normalizedOperator]
  rw [transported_mean]
  rfl

theorem lower_raw_vector [CompleteSpace E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] F) {D : F →L[ℝ] F} {oneF : F}
    (d : RankOneSpectralData D oneF) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    (ofSubordinateLower A B d hCA hβ hβr hA).eigenvector = ((0 : E), d.eigenvector) := by
  dsimp only [ofSubordinateLower, RankOneSpectralData.normalizedOperator]
  rw [transported_vector]
  rfl

theorem upper_raw_mean [CompleteSpace F]
    (A : F →L[ℝ] F) (B : E →L[ℝ] F) {D : E →L[ℝ] E} {oneE : E}
    (d : RankOneSpectralData D oneE) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    (ofSubordinateUpper A B d hCA hβ hβr hA).mean = upperMean (F := F) d := by
  dsimp only [ofSubordinateUpper, RankOneSpectralData.normalizedOperator]
  rw [transported_mean]
  rfl

theorem upper_raw_vector [CompleteSpace F]
    (A : F →L[ℝ] F) (B : E →L[ℝ] F) {D : E →L[ℝ] E} {oneE : E}
    (d : RankOneSpectralData D oneE) {CA β : ℝ}
    (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n) :
    (ofSubordinateUpper A B d hCA hβ hβr hA).eigenvector =
      upperVector (d.rate⁻¹ • A) (d.rate⁻¹ • B) d := by
  dsimp only [ofSubordinateUpper, RankOneSpectralData.normalizedOperator]
  rw [transported_vector]
  rfl

/-- The S/R-lifted global eigenfunction restricts exactly to the actual
bounded-layer eigenfunction; no gluing error remains. -/
theorem lifted_vector_restriction
    (S : F →L[ℝ] E) (R : E →L[ℝ] F) {B : F →L[ℝ] F}
    (hB : B = R.comp S) {one : F} (d : RankOneSpectralData B one) :
    R (liftedVector S d) = d.eigenvector := by
  change R (d.rate⁻¹ • S d.eigenvector) = d.eigenvector
  rw [map_smul]
  have he : R (S d.eigenvector) = B d.eigenvector :=
    (congrArg (fun A : F →L[ℝ] F => A d.eigenvector) hB).symm
  rw [he, d.right_eigenvector, smul_smul, inv_mul_cancel₀ d.rate_pos.ne', one_smul]

end RawData

section LowerAggregate

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L : Set X) (hL : MeasurableSet L)
  (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
  (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C hSF L hL)
    (1 : (Lᶜ : Set X) →ᵇ ℝ))
  {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
  (hA : ∀ n : ℕ, ‖lowerOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)

local notation "Dglobal" => globalDataWithSubordinateLower C hSF L hL hsupport d hCA hβ hβr hA

theorem lower_global_rate : (Dglobal).rate = d.rate := by
  change (ofSubordinateLower (lowerOperator C hSF L hL)
    (couplingOperator C hSF L hL) d hCA hβ hβr hA).rate = d.rate
  exact ofSubordinateLower_rate _ _ d hCA hβ hβr hA

theorem lower_global_vector :
    (Dglobal).eigenvector = d.rate⁻¹ • extensionOperator C hSF Lᶜ hL.compl d.eigenvector := by
  change (ofSubordinateLower (lowerOperator C hSF L hL)
    (couplingOperator C hSF L hL) d hCA hβ hβr hA).rate⁻¹ •
      smoothAssembly C hSF L hL
        (ofSubordinateLower (lowerOperator C hSF L hL)
          (couplingOperator C hSF L hL) d hCA hβ hβr hA).eigenvector = _
  rw [ofSubordinateLower_rate, lower_raw_vector]
  congr 1
  change extensionOperator C hSF L hL 0 + extensionOperator C hSF Lᶜ hL.compl d.eigenvector = _
  rw [map_zero, zero_add]

theorem lower_global_vector_zero : restrictOperator L (Dglobal).eigenvector = 0 := by
  rw [lower_global_vector C hSF L hL hsupport d hCA hβ hβr hA, map_smul]
  have hz := lower_upper_extension_eq_zero (𝕜 := ℝ) C hSF L hL hsupport
  have he := congrArg (fun T => T d.eigenvector) hz
  change restrictOperator L (extensionOperator C hSF Lᶜ hL.compl d.eigenvector) = 0 at he
  rw [he, smul_zero]

theorem lower_global_vector_restrict : restrictOperator Lᶜ (Dglobal).eigenvector = d.eigenvector := by
  rw [lower_global_vector C hSF L hL hsupport d hCA hβ hβr hA, map_smul]
  change d.rate⁻¹ • upperOperator C hSF L hL d.eigenvector = d.eigenvector
  rw [d.right_eigenvector, smul_smul, inv_mul_cancel₀ d.rate_pos.ne', one_smul]

theorem lower_global_mean (f : X →ᵇ ℝ) :
    (Dglobal).mean f =
      lowerMean (d.rate⁻¹ • lowerOperator C hSF L hL)
        (d.rate⁻¹ • couplingOperator C hSF L hL) d (restrictOperator L f) +
          d.mean (restrictOperator Lᶜ f) := by
  change (ofSubordinateLower (lowerOperator C hSF L hL)
    (couplingOperator C hSF L hL) d hCA hβ hβr hA).mean (layerRestriction L f) = _
  rw [lower_raw_mean]
  rfl

/-- The global and local dominant products have exactly the same continuous
test pairing. Subordinate entrance contributions vanish after multiplying
by the global right eigenfunction. -/
theorem lower_global_product_pairing (f : X →ᵇ ℝ) :
    (Dglobal).mean (f * (Dglobal).eigenvector) =
      d.mean ((restrictOperator Lᶜ f) * d.eigenvector) := by
  rw [lower_global_mean C hSF L hL hsupport d hCA hβ hβr hA]
  have hlo : restrictOperator L (f * (Dglobal).eigenvector) = 0 := by
    ext x
    change f x.val * (Dglobal).eigenvector x.val = 0
    have hz := congrArg (fun g : L →ᵇ ℝ => g x)
      (lower_global_vector_zero C hSF L hL hsupport d hCA hβ hβr hA)
    change (Dglobal).eigenvector x.val = 0 at hz
    rw [hz, mul_zero]
  have hup : restrictOperator Lᶜ (f * (Dglobal).eigenvector) =
      (restrictOperator Lᶜ f) * d.eigenvector := by
    ext x
    change f x.val * (Dglobal).eigenvector x.val = f x.val * d.eigenvector x
    have he := congrArg (fun g : (Lᶜ : Set X) →ᵇ ℝ => g x)
      (lower_global_vector_restrict C hSF L hL hsupport d hCA hβ hβr hA)
    change (Dglobal).eigenvector x.val = d.eigenvector x at he
    rw [he]
  rw [hlo, map_zero, zero_add, hup]

end LowerAggregate

section UpperAggregate

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L : Set X) (hL : MeasurableSet L)
  (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
  (d : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L hL) (1 : L →ᵇ ℝ))
  {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
  (hA : ∀ n : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)

local notation "Dupper" => globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hβ hβr hA

theorem upper_global_rate : (Dupper).rate = d.rate := by
  change (ofSubordinateUpper (upperOperator C hSF L hL)
    (couplingOperator C hSF L hL) d hCA hβ hβr hA).rate = d.rate
  exact ofSubordinateUpper_rate _ _ d hCA hβ hβr hA

theorem upper_global_vector_restrict : restrictOperator L (Dupper).eigenvector = d.eigenvector := by
  let db := ofSubordinateUpper (upperOperator C hSF L hL)
    (couplingOperator C hSF L hL) d hCA hβ hβr hA
  have he := lifted_vector_restriction (smoothAssembly C hSF L hL) (layerRestriction L)
    (restriction_assembly_eq_block C hSF L hL hsupport).symm db
  have hfst := congrArg Prod.fst he
  change restrictOperator L (Dupper).eigenvector = db.eigenvector.1 at hfst
  rw [upper_raw_vector] at hfst
  exact hfst

theorem upper_global_mean (f : X →ᵇ ℝ) : (Dupper).mean f = d.mean (restrictOperator L f) := by
  change (ofSubordinateUpper (upperOperator C hSF L hL)
    (couplingOperator C hSF L hL) d hCA hβ hβr hA).mean (layerRestriction L f) = _
  rw [upper_raw_mean]
  rfl

/-- Extending the dominant lower aggregate by subordinate upper levels
preserves the product pairing exactly. -/
theorem upper_global_product_pairing (f : X →ᵇ ℝ) :
    (Dupper).mean (f * (Dupper).eigenvector) =
      d.mean ((restrictOperator L f) * d.eigenvector) := by
  rw [upper_global_mean C hSF L hL hsupport d hCA hβ hβr hA]
  congr 1
  ext x
  change f x.val * (Dupper).eigenvector x.val = f x.val * d.eigenvector x
  have he := congrArg (fun g : L →ᵇ ℝ => g x)
    (upper_global_vector_restrict C hSF L hL hsupport d hCA hβ hβr hA)
  change (Dupper).eigenvector x.val = d.eigenvector x at he
  rw [he]

end UpperAggregate

section ActualProducts

open LayerQuasiErgodic

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)

theorem global_product_integral
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ))
    (f : X →ᵇ ℝ) :
    (∫ y, f y ∂productMeasure C hSF d) = d.mean (f * d.eigenvector) := by
  rw [productMeasure, LeanShared.integral_eigenvectorMeasure _ _ d.eigenvector.continuous.measurable
    (d.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF))]
  exact (d.eigenmeasure_represents (actual_transfer_positive C hSF) (f * d.eigenvector)).symm

/-- The actual global product measure is exactly the ambient pushforward of
the dominant upper local product. Support and zero-noise stability therefore
transfer from the local theorem. -/
theorem lower_global_product_eq_local_map
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C hSF L hL)
      (1 : (Lᶜ : Set X) →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖lowerOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)
    (μ : Measure (Lᶜ : Set X)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (Lᶜ : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) :
    productMeasure C hSF (globalDataWithSubordinateLower C hSF L hL hsupport d hCA hβ hβr hA) =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val := by
  let dg := globalDataWithSubordinateLower C hSF L hL hsupport d hCA hβ hβr hA
  have : IsProbabilityMeasure (productMeasure C hSF dg) :=
    eigenvector_product_isProbability dg (leadingMeasure C hSF dg)
      (dg.eigenmeasure_represents (actual_transfer_positive C hSF))
      (dg.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF))
  have : IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) :=
    eigenvector_product_isProbability d μ hmean hg0
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable measurable_subtype_coe f.continuous.measurable.stronglyMeasurable,
    global_product_integral C hSF dg f,
    lower_global_product_pairing C hSF L hL hsupport d hCA hβ hβr hA f,
    LeanShared.integral_eigenvectorMeasure μ d.eigenvector d.eigenvector.continuous.measurable hg0]
  exact hmean ((restrictOperator Lᶜ f) * d.eigenvector)

/-- Adding pressure-small upper levels leaves the actual dominant lower
product measure unchanged after inclusion into the ambient state space. -/
theorem upper_global_product_eq_local_map
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L hL) (1 : L →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)
    (μ : Measure L) [IsFiniteMeasure μ]
    (hmean : ∀ f : L →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) :
    productMeasure C hSF (globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hβ hβr hA) =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val := by
  let dg := globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hβ hβr hA
  have : IsProbabilityMeasure (productMeasure C hSF dg) :=
    eigenvector_product_isProbability dg (leadingMeasure C hSF dg)
      (dg.eigenmeasure_represents (actual_transfer_positive C hSF))
      (dg.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF))
  have : IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) :=
    eigenvector_product_isProbability d μ hmean hg0
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable measurable_subtype_coe f.continuous.measurable.stronglyMeasurable,
    global_product_integral C hSF dg f,
    upper_global_product_pairing C hSF L hL hsupport d hCA hβ hβr hA f,
    LeanShared.integral_eigenvectorMeasure μ d.eigenvector d.eigenvector.continuous.measurable hg0]
  exact hmean ((restrictOperator L f) * d.eigenvector)

omit [CompactSpace X] in
/-- Inclusion of a live stratum sends every local support point to an
ambient support point of the pushed measure. -/
theorem subtype_support_maps_into {U : Set X} (μ : Measure U) {x : U} (hx : x ∈ μ.support) :
    x.val ∈ (μ.map Subtype.val).support := by
  rw [Measure.support_eq_forall_isOpen] at hx ⊢
  intro V hxV hV
  rw [Measure.map_apply measurable_subtype_coe hV.measurableSet]
  exact hx (Subtype.val ⁻¹' V) hxV (hV.preimage continuous_subtype_val)

/-- Local basic-set support passes to the constructed global product. -/
theorem lower_global_support_contains_local_core
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C hSF L hL)
      (1 : (Lᶜ : Set X) →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖lowerOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)
    (μ : Measure (Lᶜ : Set X)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (Lᶜ : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) (Λ : Set (Lᶜ : Set X))
    (hΛ : Λ ⊆ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    Subtype.val '' Λ ⊆
      (productMeasure C hSF (globalDataWithSubordinateLower C hSF L hL hsupport d hCA hβ hβr hA)).support := by
  rw [lower_global_product_eq_local_map C hSF L hL hsupport d hCA hβ hβr hA μ hmean hg0]
  rintro _ ⟨x, hx, rfl⟩
  exact subtype_support_maps_into _ (hΛ hx)

/-- Support of the dominant lower aggregate survives extension by upper
subordinate levels. -/
theorem upper_global_support_contains_local_core
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L hL) (1 : L →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)
    (μ : Measure L) [IsFiniteMeasure μ]
    (hmean : ∀ f : L →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) (Λ : Set L)
    (hΛ : Λ ⊆ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    Subtype.val '' Λ ⊆
      (productMeasure C hSF (globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hβ hβr hA)).support := by
  rw [upper_global_product_eq_local_map C hSF L hL hsupport d hCA hβ hβr hA μ hmean hg0]
  rintro _ ⟨x, hx, rfl⟩
  exact subtype_support_maps_into _ (hΛ hx)

/-- Qualified uniqueness of the actual global QEM follows from local
basic-set positivity; competing global measures need only support that core. -/
theorem lower_global_qualified_uniqueness
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C hSF L hL)
      (1 : (Lᶜ : Set X) →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖lowerOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)
    (Λ : Set (Lᶜ : Set X)) (hΛ : Λ.Nonempty) (hpos : ∀ x ∈ Λ, 0 < d.eigenvector x)
    (ν : Measure X) (hq : C.IsQuasiErgodic ν) (hsupp : Subtype.val '' Λ ⊆ ν.support) :
    ν = productMeasure C hSF (globalDataWithSubordinateLower C hSF L hL hsupport d hCA hβ hβr hA) := by
  let dg := globalDataWithSubordinateLower C hSF L hL hsupport d hCA hβ hβr hA
  apply QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support C (transferOperator C hSF)
    (transferOperator_apply C hSF) dg (leadingMeasure C hSF dg)
    (dg.eigenmeasure_represents (actual_transfer_positive C hSF))
    (dg.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF))
    (Subtype.val '' Λ) (hΛ.image _) _ ν hq hsupp
  rintro _ ⟨x, hx, rfl⟩
  have he := congrArg (fun g : (Lᶜ : Set X) →ᵇ ℝ => g x)
    (lower_global_vector_restrict C hSF L hL hsupport d hCA hβ hβr hA)
  change dg.eigenvector x.val = d.eigenvector x at he
  rw [he]
  exact hpos x hx

/-- The analogous qualified uniqueness after adding upper subordinate levels. -/
theorem upper_global_qualified_uniqueness
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L hL) (1 : L →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n)
    (Λ : Set L) (hΛ : Λ.Nonempty) (hpos : ∀ x ∈ Λ, 0 < d.eigenvector x)
    (ν : Measure X) (hq : C.IsQuasiErgodic ν) (hsupp : Subtype.val '' Λ ⊆ ν.support) :
    ν = productMeasure C hSF (globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hβ hβr hA) := by
  let dg := globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hβ hβr hA
  apply QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support C (transferOperator C hSF)
    (transferOperator_apply C hSF) dg (leadingMeasure C hSF dg)
    (dg.eigenmeasure_represents (actual_transfer_positive C hSF))
    (dg.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF))
    (Subtype.val '' Λ) (hΛ.image _) _ ν hq hsupp
  rintro _ ⟨x, hx, rfl⟩
  have he := congrArg (fun g : L →ᵇ ℝ => g x)
    (upper_global_vector_restrict C hSF L hL hsupport d hCA hβ hβr hA)
  change dg.eigenvector x.val = d.eigenvector x at he
  rw [he]
  exact hpos x hx

end ActualProducts

end ConditionedStochasticStabilityHyperbolic.Global.LayerProductCorrespondence
