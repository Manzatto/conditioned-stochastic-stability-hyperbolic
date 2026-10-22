module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseMaps

/-! Cartesian-product regular noise, with the only deferred facts being
ordinary deterministic fractional product calculus. Joint parameter C¹,
rank, atlas construction, and uniform scale/coordinate control are proved
from the literal factor data. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [Fintype ι] [Fintype κ]

local instance productRegularNoiseConstructorLocal1 : ChartedSpace (E × F) (X × Y) := productCharts

/-- Precise ordinary fractional Cartesian-product calculus. The derivative
bound is in the constructed finite product charts and uses maximum norms.
Regularity is retained among its hypotheses: bounds on formal derivatives
alone do not imply the product differentiation formula. -/
structure FractionalProductCalculus (r : ℝ) : Prop where
  regular : ∀ (f : X → X) (g : Y → Y),
    LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r f →
    LeanShared.FractionalManifoldRegularity.Regular (E := F) (F := F) r g →
    LeanShared.FractionalManifoldRegularity.Regular (E := E × F) (F := E × F) r (Prod.map f g)
  whitney : ∀ (T0 f : X → X) (T1 g : Y → Y)
    (A : WhitneyAtlas (E := E) T0) (B : WhitneyAtlas (E := F) T1),
    LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T0 →
    LeanShared.FractionalManifoldRegularity.Regular (E := F) (F := F) r T1 →
    LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r f →
    LeanShared.FractionalManifoldRegularity.Regular (E := F) (F := F) r g →
    ∀ δ δ', A.Bound r f δ → B.Bound r g δ' →
      (A.product B).Bound r (Prod.map f g) (max δ δ')

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ, E)) ∞ X] [IsManifold (𝓘(ℝ, F)) ∞ Y] in
private theorem WhitneyAtlas.Bound.mono {T0 f : X → X} (A : WhitneyAtlas (E := E) T0)
    {r δ δ' : ℝ} (h : A.Bound r f δ) (hδ : δ ≤ δ') : A.Bound r f δ' where
  uniform x := (h.uniform x).trans hδ
  target_control := h.target_control
  derivatives i k hk y hy := (h.derivatives i k hk y hy).trans hδ
  holder hr i y hy z hz := (h.holder hr i y hy z hz).trans
    (mul_le_mul_of_nonneg_right hδ (Real.rpow_nonneg (norm_nonneg _) _))

/-- Actual product Maps. The common window and linear Whitney constant are
chosen internally; all component restrictions use the literal cube. -/
def productMaps {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}
    (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := F) (ι := κ) T' r)
    (hT : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (hT' : LeanShared.FractionalManifoldRegularity.Regular (E := F) (F := F) r T')
    (calculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) r) :
    Maps (E := E × F) (ι := ι ⊕ κ) (T.prodCongr T') r where
  window := min P.window Q.window
  window_positive := lt_min P.window_positive Q.window_positive
  family := independentFamily P Q
  atlas := P.atlas.product Q.atlas
  constant := max P.constant Q.constant
  constant_positive := P.constant_positive.trans_le (le_max_left _ _)
  map_regular ε hε hw v := calculus.regular _ _
    (P.map_regular ε hε (le_min_iff.mp hw).1
      (LeanShared.NoiseCubeRescaling.splitCube (ε : ℝ) v).1)
    (Q.map_regular ε hε (le_min_iff.mp hw).2
      (LeanShared.NoiseCubeRescaling.splitCube (ε : ℝ) v).2)
  joint_C1 := independentFamily_joint_C1 P Q
  control_surjective ε hε hw v z := by
    rw [modelWithCornersSelf_prod]
    exact independentFamily_control_surjective P Q ε hε hw v z
  whitney_bound ε hε hw v := by
    let vl : cube (ι := ι) ε := (LeanShared.NoiseCubeRescaling.splitCube (ε : ℝ) v).1
    let vr : cube (ι := κ) ε := (LeanShared.NoiseCubeRescaling.splitCube (ε : ℝ) v).2
    have hp := P.map_regular ε hε (le_min_iff.mp hw).1 vl
    have hq := Q.map_regular ε hε (le_min_iff.mp hw).2 vr
    have hb := calculus.whitney T (P.family ε vl.val) T' (Q.family ε vr.val)
      P.atlas Q.atlas hT hT' hp hq _ _
      (P.whitney_bound ε hε (le_min_iff.mp hw).1 vl)
      (Q.whitney_bound ε hε (le_min_iff.mp hw).2 vr)
    apply hb.mono (P.atlas.product Q.atlas)
    apply max_le
    · exact (mul_le_mul_of_nonneg_left (show ‖vl.val‖ ≤ ‖v.val‖ from
        (pi_norm_le_iff_of_nonneg (norm_nonneg v.val)).mpr
          (fun i => norm_le_pi_norm v.val (.inl i))) P.constant_positive.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact (mul_le_mul_of_nonneg_left (show ‖vr.val‖ ≤ ‖v.val‖ from
        (pi_norm_le_iff_of_nonneg (norm_nonneg v.val)).mpr
          (fun j => norm_le_pi_norm v.val (.inr j))) Q.constant_positive.le).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
