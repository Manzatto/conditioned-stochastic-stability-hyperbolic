module

public import LeanShared.Analysis.GraphLeafNorm
public import LeanShared.Analysis.CompactnessFromComponents
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Local Ascoli compactness in the actual graph-leaf norm

A family of continuous functions with a common fast polynomial envelope and
local equicontinuity is relatively compact in the supremum of genuine graph
L¹ spaces. Compactness of its image is proved, not supplied as an assumption.
The quantitative graph-volume/tail estimate comes from `GraphLeafNorm`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace LeanShared.GraphLeafNorm

variable {U E I : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure U) [μ.IsAddHaarMeasure]
  {J r A : ℝ} (hJ : 0 ≤ J) (hr : (Module.finrank ℝ U : ℝ) < r) (hA : 0 ≤ A)
  (f : I → E →ᵇ ℂ)
  (hfast : ∀ i x, ‖f i x‖ ≤ A * radialWeight (2 * r) x)

/-- The family represented in the actual complete graph-leaf L¹ norm. -/
def leafFamily (i : I) : LeafSpace (E := E) μ (J := J) :=
  ofDecayingFunction μ (hJ := hJ) (hr := hr) (hf := (f i).continuous.measurable)
    (hA := hA) (hdecay := fastDecay_le_slow hA (exponent_pos hr).le (hfast i))

omit [MeasurableSpace E] [BorelSpace E] in
omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
include hr hA hfast in
theorem family_norm_le (i : I) (x : E) : ‖f i x‖ ≤ A :=
  (hfast i x).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (radialWeight_le_one (by linarith [exponent_pos hr]) x) hA)

omit [MeasurableSpace E] [BorelSpace E] in
omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
include hr hA hfast in
/-- Arzelà--Ascoli gives actual compact control images on every closed ball. -/
theorem isCompact_closure_restricted_family
    (H : Equicontinuous (fun i x => f i x)) (R : ℝ) :
    IsCompact (closure (Set.range (fun i => (f i).domRestrict (closedBall (0 : E) R)))) := by
  classical
  let q := fun i => (f i).domRestrict (closedBall (0 : E) R)
  let : CompactSpace (closedBall (0 : E) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) R)
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) A)
    (isCompact_closedBall (0 : ℂ) A)
  · rintro _ x ⟨i, rfl⟩
    exact mem_closedBall_zero_iff.mpr (family_norm_le hr hA f hfast i x.val)
  · intro x V hV
    have h := (continuous_subtype_val.tendsto x).eventually (H x.val V hV)
    filter_upwards [h] with y hy
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact hy i

include hJ hr hA hfast in
/-- Fast radial decay and equicontinuity imply genuine graph-leaf norm
compactness by local Ascoli plus uniform, proved leaf tails. -/
theorem isCompact_closure_leafFamily
    (H : Equicontinuous (fun i x => f i x)) :
    IsCompact (closure (Set.range (leafFamily μ hJ hr hA f hfast))) := by
  classical
  let q : ∀ R : ℝ, I → (closedBall (0 : E) R →ᵇ ℂ) :=
    fun R i => (f i).domRestrict (closedBall (0 : E) R)
  have hq (R : ℝ) : TotallyBounded (q R '' (Set.univ : Set I)) := by
    simpa only [Set.image_univ] using
      (isCompact_closure_restricted_family hr hA f hfast H R).totallyBounded.subset subset_closure
  have hpow : Tendsto (fun R : ℝ => (1 + R) ^ (-r)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (exponent_pos hr)).comp
      (tendsto_atTop_mono (fun R : ℝ => le_add_of_nonneg_left zero_le_one) tendsto_id)
  have htail : Tendsto (fun R : ℝ => (2 * A * (1 + R) ^ (-r)) * J *
      ∫ u, radialWeight r u ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds.mul hpow).mul_const J).mul_const (∫ u, radialWeight r u ∂μ)
  have hc : ∀ ε > 0, ∃ R : ℝ, ∃ δ > 0,
      TotallyBounded (q R '' (Set.univ : Set I)) ∧
      ∀ i ∈ (Set.univ : Set I), ∀ j ∈ (Set.univ : Set I),
        dist (q R i) (q R j) < δ →
        dist (leafFamily μ hJ hr hA f hfast i) (leafFamily μ hJ hr hA f hfast j) < ε := by
    intro ε hε
    have hevent := (tendsto_order.mp htail).2 (ε / 2) (by linarith)
    obtain ⟨R, hsmall, hR⟩ := (hevent.and (eventually_ge_atTop (0 : ℝ))).exists
    let B := J * (μ (closedBall (0 : U) R)).toReal
    have hB : 0 ≤ B := mul_nonneg hJ ENNReal.toReal_nonneg
    let δ := (ε / 2) / (B + 1)
    have hB1 : 0 < B + 1 := by positivity
    have hδ : 0 < δ := by dsimp [δ]; positivity
    refine ⟨R, δ, hδ, hq R, ?_⟩
    intro i _ j _ hij
    have hlocal : ∀ x, ‖x‖ ≤ R → ‖f i x - f j x‖ ≤ δ := by
      intro x hx
      have hx' : x ∈ closedBall (0 : E) R := mem_closedBall_zero_iff.mpr hx
      have hp := BoundedContinuousFunction.dist_coe_le_dist
        (f := q R i) (g := q R j) (⟨x, hx'⟩ : closedBall (0 : E) R)
      have hh : ‖f i x - f j x‖ < δ := by
        simpa only [q, BoundedContinuousFunction.domRestrict_apply, dist_eq_norm]
          using hp.trans_lt hij
      exact hh.le
    have hnorm := norm_sub_ofDecayingFunction_le μ hJ hr hA
      (f i).continuous.measurable (f j).continuous.measurable (hfast i) (hfast j)
      hR hδ.le hlocal
    have hprod : δ * B < ε / 2 := by
      have hcancel : δ * (B + 1) = ε / 2 := div_mul_cancel₀ _ hB1.ne'
      nlinarith
    rw [dist_eq_norm]
    dsimp only [leafFamily]
    dsimp only [B] at hprod
    nlinarith [hnorm]
  simpa only [Set.image_univ] using
    CompactnessFromComponents.isCompact_closure_image_of_controls Set.univ
      (leafFamily μ hJ hr hA f hfast) q hc

end LeanShared.GraphLeafNorm
