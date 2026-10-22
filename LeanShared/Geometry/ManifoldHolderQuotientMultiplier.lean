module
public import LeanShared.Geometry.ManifoldHolderQuotientConjugation
public import LeanShared.Geometry.BoundedHolderMultiplication
public import LeanShared.Geometry.CompactSmoothHolderGraph
public import LeanShared.Geometry.SupportedChartExtension
public import LeanShared.Geometry.ChartLocalization
public import LeanShared.Analysis.CompactSchwartzCutoff

/-! Multiplication by a smooth global function on the constructed
lower-regularity manifold space (finite product of Euclidean little Hölder chart
spaces modulo the reconstruction kernel). On chart `i` multiply by the smooth
compactly supported `a_i = ζ_i (ψ ∘ κ_i⁻¹)`, with `ζ_i = 1` on the closed chart
region; this preserves each Euclidean little Hölder space, reconstructs to
`ψ · (reconstruction z)`, and descends to the quotient with the operator bound of
the coordinate multiplication. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set
open scoped Manifold ContDiff BoundedContinuousFunction SchwartzMap

namespace LeanShared.EuclideanSmoothHolderCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {V : Set E} (hV : IsCompact (closure V))
  {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (A : BoundedHolderSpace.graph E b) (a : E → ℂ) (ha : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ a)
  (hA : ∀ y, BoundedHolderSpace.physical E b A y = a y)

include hA in
theorem graph_core_product (c : SmoothSupportedManifoldCore.core (E := E) V) :
    BoundedHolderSpace.product b A (core hV hb hb1 c) =
      core hV hb hb1 (SmoothSupportedManifoldCore.multiplier V a ha c) := by
  apply BoundedHolderSpace.physical_injective E b
  ext x
  rw [BoundedHolderSpace.physical_product, BoundedContinuousFunction.mul_apply, hA]
  change a x * c.val x = c.val x * a x
  ring

include ha hA in
theorem product_mapsTo (v : space hV hb hb1) :
    BoundedHolderSpace.product b A v.val ∈ space hV hb hb1 := by
  refine (smooth_dense hV hb hb1).induction_on
    (p := fun z => BoundedHolderSpace.product b A z.val ∈ space hV hb hb1) v
    (((core hV hb hb1).range.isClosed_topologicalClosure).preimage
      ((BoundedHolderSpace.multiply b A).continuous.comp continuous_subtype_val)) ?_
  intro c
  change BoundedHolderSpace.product b A (core hV hb hb1 c) ∈ _
  rw [graph_core_product hV hb hb1 A a ha hA]
  exact (core hV hb hb1).range.le_topologicalClosure ⟨_, rfl⟩

/-- Multiplication by `A` on the Euclidean little Hölder space. -/
@[expose] def multiplyOn : space hV hb hb1 →L[ℂ] space hV hb hb1 :=
  ((BoundedHolderSpace.multiply b A).comp (space hV hb hb1).subtypeL).codRestrict
    (space hV hb hb1) (fun v => product_mapsTo hV hb hb1 A a ha hA v)

theorem physical_multiplyOn (v : space hV hb hb1) (y : E) :
    physical hV hb hb1 (multiplyOn hV hb hb1 A a ha hA v) y = a y * physical hV hb hb1 v y := by
  change BoundedHolderSpace.physical E b (BoundedHolderSpace.product b A v.val) y = _
  rw [BoundedHolderSpace.physical_product, BoundedContinuousFunction.mul_apply, hA]
  rfl

theorem physical_zero_outside (v : space hV hb hb1) (y : E) (hy : y ∉ closure V) :
    physical hV hb hb1 v y = 0 :=
  BoundedHolderSpace.corePhysical_zero_outside E b (smoothPhysical hV) (smooth_holder hV hb hb1)
    (closure V) (fun c _ hx => image_eq_zero_of_notMem_tsupport
      (fun h => hx (subset_closure (c.property.2 h)))) v y hy

end LeanShared.EuclideanSmoothHolderCore

namespace LeanShared.ManifoldHolderQuotient
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [Fintype I] {e : I → OpenPartialHomeomorph M E} {K : I → Set E} {V : Set M}
  (d : ChartSmoothingRegions.Data e K V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

local instance coordinatesNormed'' : NormedAddCommGroup (Coordinates d hb hb1) := inferInstance
local instance coordinatesSeminormed'' : SeminormedAddCommGroup (Coordinates d hb hb1) :=
  (coordinatesNormed'' d hb hb1).toSeminormedAddCommGroup
local instance coordinatesScalar'' : NormedSpace ℂ (Coordinates d hb hb1) := inferInstance

include hb hb1 in
/-- A smooth chart multiplier agreeing with `ψ` on the closed chart region. -/
theorem exists_chart_multiplier (atlas : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ) (i : I) :
    ∃ (a : E → ℂ) (A : BoundedHolderSpace.graph E b), ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ a ∧
      (∀ y, BoundedHolderSpace.physical E b A y = a y) ∧
      ∀ x ∈ (e i).source, e i x ∈ closure (d.region i) → a (e i x) = ψ x := by
  obtain ⟨ζ, ζc, ζin, ζone⟩ := CompactSchwartzCutoff.exists_cutoff (d.compact_closure i)
    (e i).open_target (d.closure_target i)
  let θ : M → ℂ := SupportedChartExtension.function (e i) ζ
  have hθs : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ θ :=
    SupportedChartExtension.smooth (e i) (atlas i) (ζ.smooth ⊤) ζc ζin
  have hθc : HasCompactSupport θ := SupportedChartExtension.compact_support (e i) ζc ζin
  have hθsupp : tsupport θ ⊆ (e i).source := by
    refine (SupportedChartExtension.support_subset (e i) ζc ζin).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (e i).map_target (ζin hy)
  have smooth := ChartLocalization.coordinate_contDiff (e i) θ hθsupp (atlas i) hθs hθc ψ hψ
  have compact := ChartLocalization.coordinate_hasCompactSupport (e i) θ hθsupp hθc ψ
  obtain ⟨A, hA⟩ := CompactSmoothHolderGraph.exists_graph smooth compact hb hb1.le
  refine ⟨ChartLocalization.coordinate (e i) θ ψ, A, smooth.contMDiff, hA, fun x hx hr => ?_⟩
  rw [ChartLocalization.coordinate_chart (e i) θ ψ x hx]
  have one : θ x = 1 := by
    change SupportedChartExtension.function (e i) ζ x = 1
    rw [← (e i).left_inv hx, SupportedChartExtension.coordinate (e i) (e i x) ((e i).map_source hx)]
    exact ζone _ hr
  rw [one, one_mul]

variable (atlas : ∀ i, e i ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ)

include atlas hψ in
/-- The physical multiplication by `ψ` is bounded on the lower-regularity space. -/
theorem multiplier_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Space d hb hb1, ∃ w : Space d hb hb1,
      (∀ x, physical d hb hb1 w x = ψ x * physical d hb hb1 v x) ∧ ‖w‖ ≤ B * ‖v‖ := by
  choose a A ha hA agree using exists_chart_multiplier d hb hb1 atlas ψ hψ
  let mult : Coordinates d hb hb1 →L[ℂ] Coordinates d hb hb1 :=
    ContinuousLinearMap.pi fun i =>
      (EuclideanSmoothHolderCore.multiplyOn (d.compact_closure i) hb hb1 (A i) (a i) (ha i)
        (hA i)).comp (ContinuousLinearMap.proj i)
  have recon (z : Coordinates d hb hb1) (x : M) :
      reconstruction d hb hb1 (mult z) x = ψ x * reconstruction d hb hb1 z x := by
    rw [reconstruction_apply', reconstruction_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ (e i).source
    · simp only [SupportedChartExtension.function, hx, ite_true]
      change EuclideanSmoothHolderCore.physical (d.compact_closure i) hb hb1
        (EuclideanSmoothHolderCore.multiplyOn (d.compact_closure i) hb hb1 (A i) (a i) (ha i)
          (hA i) (z i)) (e i x) = _
      rw [EuclideanSmoothHolderCore.physical_multiplyOn]
      by_cases hr : e i x ∈ closure (d.region i)
      · rw [agree i x hx hr]
      · rw [EuclideanSmoothHolderCore.physical_zero_outside _ hb hb1 _ _ hr, mul_zero, mul_zero]
    · simp only [SupportedChartExtension.function, hx, ite_false, mul_zero]
  refine ⟨‖mult‖, norm_nonneg _, fun v => ?_⟩
  obtain ⟨z0, rfl⟩ := BanachFunctionQuotient.quotient_surjective (𝕜 := ℂ)
    (H := Coordinates d hb hb1) (X := M) (F := ℂ) (reconstruction d hb hb1) v
  refine ⟨quotient d hb hb1 (mult z0), fun x => ?_, ?_⟩
  · exact recon z0 x
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hm : 0 ≤ ‖mult‖ := norm_nonneg _
    obtain ⟨z, hz, small⟩ := Submodule.Quotient.norm_mk_lt (S := (reconstruction d hb hb1).ker)
      (quotient d hb hb1 z0) (show 0 < ε / (‖mult‖ + 1) by positivity)
    have same : quotient d hb hb1 (mult z0) = quotient d hb hb1 (mult z) := by
      apply physical_injective d hb hb1
      ext x
      have h := congrArg (fun w => physical d hb hb1 w x) hz
      change reconstruction d hb hb1 (mult z0) x = reconstruction d hb hb1 (mult z) x
      rw [recon, recon, show reconstruction d hb hb1 z x = reconstruction d hb hb1 z0 x from h]
    rw [same]
    calc ‖quotient d hb hb1 (mult z)‖ ≤ ‖mult z‖ := Submodule.Quotient.norm_mk_le _ _
      _ ≤ ‖mult‖ * ‖z‖ := mult.le_opNorm z
      _ ≤ ‖mult‖ * (‖quotient d hb hb1 z0‖ + ε / (‖mult‖ + 1)) :=
          mul_le_mul_of_nonneg_left small.le hm
      _ < ‖mult‖ * ‖quotient d hb hb1 z0‖ + ε := by
          rw [mul_add]
          have : ‖mult‖ * (ε / (‖mult‖ + 1)) < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith
          linarith

end LeanShared.ManifoldHolderQuotient
