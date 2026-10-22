module

public import LeanShared.Analysis.SchwartzAmbientBlocks
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Specified leaf families separate smooth core functions

Coverage by supports of actual leaf measures makes the Schwartz realization
injective. For the genuine cone partition, physical block separation and
nonzero weights then make the actual supported block core map injective.
Coverage is also derived for families containing all constant affine graph
planes with their literal pushforward parameter measures. Identifying those
measures with geometric manifold area remains a separate classical bridge.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction ENNReal

namespace LeanShared.LeafFamilySeparation

/-- Continuous almost-everywhere equality holds at every support point. -/
theorem eq_of_ae_eq_at_support {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [T2Space Y] (ν : Measure X) (f g : X → Y)
    (hf : Continuous f) (hg : Continuous g) (hae : f =ᵐ[ν] g)
    (x : X) (hx : x ∈ ν.support) : f x = g x :=
  ν.support_subset_of_isClosed (isClosed_eq hf hg) hae hx

section Realization

variable {E U A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (hcover : ∀ x : E, ∃ a, x ∈ ((leaves a).measure μ).support)

include hcover in
theorem realization_injective : Function.Injective (SchwartzAmbientRealization.realization μ hJ leaves) := by
  intro f g hfg
  ext x
  obtain ⟨a, ha⟩ := hcover x
  have hcoord : SchwartzAmbientRealization.realization μ hJ leaves f a =
      SchwartzAmbientRealization.realization μ hJ leaves g a := congrArg (fun z => z a) hfg
  have hae : (f : E → ℂ) =ᵐ[(leaves a).measure μ] g := by
    apply (SchwartzAmbientRealization.realization_ae μ hJ leaves f a).symm.trans
    rw [hcoord]
    exact SchwartzAmbientRealization.realization_ae μ hJ leaves g a
  exact eq_of_ae_eq_at_support _ f g f.continuous g.continuous hae x ha

include hcover in
theorem linearMap_injective : Function.Injective (SchwartzAmbientRealization.linearMap μ hJ leaves) :=
  realization_injective μ hJ leaves hcover

end Realization

section Core

variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (hcover : ∀ x : E, ∃ a, x ∈ ((leaves a).measure μ).support)
  (D : Set E) {Cplus Cminus : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
  (Φ : ConeDyadicSymbols.AngularCutoff Cplus Cminus) (t : Bool → ℝ)
  (hbounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D
    (ConeDyadicSymbols.symbols χ Φ) t)

include hcover in
/-- The actual block core is injective for the genuine cone partition.
Neither a core-injectivity field nor a block-separation hypothesis is used. -/
theorem coreMap_injective : Function.Injective (SchwartzAmbientBlocks.coreMap μ hJ leaves D
    (ConeDyadicSymbols.symbols χ Φ) t hbounded) := by
  intro f g hfg
  have hz : SchwartzAmbientBlocks.coreMap μ hJ leaves D
      (ConeDyadicSymbols.symbols χ Φ) t hbounded (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hblocks : ∀ j : ℕ × Bool,
      ConeFourierBlocks.block (ConeDyadicSymbols.symbols χ Φ j) (f - g).val = 0 := by
    intro j
    have hj := congrArg (fun z => z j) hz
    change SchwartzAmbientBlocks.weight t j •
      SchwartzAmbientRealization.linearMap μ hJ leaves
        (ConeFourierBlocks.block (ConeDyadicSymbols.symbols χ Φ j) (f - g).val) = 0 at hj
    have hw : SchwartzAmbientBlocks.weight t j ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
    have hb := (smul_eq_zero.mp hj).resolve_left hw
    apply linearMap_injective μ hJ leaves hcover
    rw [map_zero]
    exact hb
  have he := ConeFourierBlocks.eq_zero_of_blocks_zero χ Φ (f - g).val hblocks
  apply sub_eq_zero.mp
  exact Subtype.ext he

end Core

section GraphSupports

variable {E U : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [MeasurableSpace U] {J : ℝ}

/-- A continuous graph sends parameter support into its actual ambient
pushforward measure support. -/
theorem graph_mem_support (μ : Measure U) (L : GraphLeafNorm.GraphLeaf U E J)
    (hc : Continuous L.graph) (u : U) (hu : u ∈ (L.sourceMeasure μ).support) :
    L.graph u ∈ (L.measure μ).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro V huV hV
  rw [GraphLeafNorm.GraphLeaf.measure, Measure.map_apply L.measurable_graph hV.measurableSet]
  exact (Measure.mem_support_iff_forall u).mp hu _ ((hV.preimage hc).mem_nhds huV)

/-- Full-support parameter laws and continuous graphs covering the ambient
points derive leaf-measure support coverage. This can be applied to affine
reference planes in arbitrary continuous linear coordinates. -/
theorem coverage_of_full_parameter_graphs {A : Type*} (μ : Measure U) [μ.IsOpenPosMeasure]
    (leaves : A → GraphLeafNorm.GraphLeaf U E J)
    (hcontinuous : ∀ a, Continuous (leaves a).graph)
    (hsource : ∀ a, (leaves a).sourceMeasure μ = μ)
    (hpoints : ∀ x : E, ∃ a, ∃ u, (leaves a).graph u = x) :
    ∀ x : E, ∃ a, x ∈ ((leaves a).measure μ).support := by
  intro x
  obtain ⟨a, u, hax⟩ := hpoints x
  have hu : u ∈ ((leaves a).sourceMeasure μ).support := by
    rw [hsource a, Measure.support_eq_univ]
    trivial
  refine ⟨a, ?_⟩
  rw [← hax]
  exact graph_mem_support μ (leaves a) (hcontinuous a) u hu

end GraphSupports

section AffinePlanes

variable {U V A : Type*} [NormedAddCommGroup U] [MeasurableSpace U]
  [NormedAddCommGroup V] [MeasurableSpace V]
  (J : ℝ) (hJ : 1 ≤ J)

/-- A full affine reference plane with literal density one. -/
def affinePlane (v : V) : GraphLeafNorm.GraphLeaf U (U × V) J :=
  GraphLeafNorm.GraphLeaf.ofFunction (fun _ : U => v) measurable_const univ MeasurableSet.univ
    (fun _ => 1) measurable_const (fun _ => by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hJ)

theorem affinePlane_sourceMeasure (μ : Measure U) (v : V) :
    (affinePlane (U := U) J hJ v).sourceMeasure μ = μ := by
  simp only [GraphLeafNorm.GraphLeaf.sourceMeasure, affinePlane, GraphLeafNorm.GraphLeaf.ofFunction,
    Measure.restrict_univ]
  exact withDensity_one

variable [BorelSpace (U × V)] (μ : Measure U) [μ.IsOpenPosMeasure]
  (leaves : A → GraphLeafNorm.GraphLeaf U (U × V) J)
  (hplanes : ∀ v : V, ∃ a, leaves a = affinePlane (U := U) J hJ v)

include hplanes in
/-- A family containing every affine reference plane automatically covers
the ambient space by supports of its literal graph measures. -/
theorem coverage_of_affinePlanes : ∀ x : U × V, ∃ a, x ∈ ((leaves a).measure μ).support := by
  intro x
  obtain ⟨a, ha⟩ := hplanes x.2
  refine ⟨a, ?_⟩
  rw [ha]
  have hu : x.1 ∈ ((affinePlane (U := U) J hJ x.2).sourceMeasure μ).support := by
    rw [affinePlane_sourceMeasure J hJ μ x.2, Measure.support_eq_univ]
    trivial
  exact graph_mem_support μ (affinePlane (U := U) J hJ x.2)
    (continuous_id.prodMk continuous_const) x.1 hu

end AffinePlanes

end LeanShared.LeafFamilySeparation
