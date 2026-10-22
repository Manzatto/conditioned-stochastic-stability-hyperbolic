module

public import ConditionedStochasticStabilityHyperbolic.Paper.LinearRechartedWhitneyAtlas
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductControlGeometry
public import LeanShared.Geometry.LinearRechartedIdentity
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! The actual noise family, joint C¹ extension and full control rank
survive the constructed linear model change. Only ordinary fractional
linear-composition calculus remains a stated classical source. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LinearRechartedManifold

variable {E F M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [Fintype ι] {T : M ≃ₜ M} {r : ℝ}

/-- A single explicit bound covers all derivative orders and the fractional
Hölder term under linear conjugation. -/
def linearModelConstant (e : E ≃L[ℝ] F) (r : ℝ) : ℝ :=
  max 1 ‖e.toContinuousLinearMap‖ * (max 1 ‖e.symm.toContinuousLinearMap‖) ^ (⌊r⌋₊ + 1)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem linearModelConstant_positive (e : E ≃L[ℝ] F) (r : ℝ) :
    0 < linearModelConstant e r :=
  mul_pos (zero_lt_one.trans_le (le_max_left _ _))
    (pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _)

/-- Ordinary deterministic C^r invariance and the quantitative finite-chart
linear conjugation bound. The scale is fixed by the actual equivalence,
not an arbitrary parameter-dependent constant. -/
structure LinearFractionalCalculus (e : E ≃L[ℝ] F) (r : ℝ) : Prop where
  regular : ∀ f : M → M, FractionalManifoldRegularity.Regular (E := E) (F := E) r f →
    letI := charts (M := M) e;
      FractionalManifoldRegularity.Regular (E := F) (F := F) r f
  whitney : ∀ (f : M → M) (A : WhitneyAtlas (E := E) T) (δ : ℝ),
    FractionalManifoldRegularity.Regular (E := E) (F := E) r T →
    FractionalManifoldRegularity.Regular (E := E) (F := E) r f → A.Bound r f δ →
    letI := charts (M := M) e;
      (A.linearRechart e).Bound r f (linearModelConstant e r * δ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- Actual joint parameter regularity after recharting. -/
theorem linearRechart_joint_C1 (e : E ≃L[ℝ] F) (P : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ P.window) :
    letI := charts (M := M) e;
    ∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, F))) (𝓘(ℝ, F)) 1
        (fun z : Control (ι := ι) × M => P.family ε z.1 z.2) (O ×ˢ univ) := by
  let := charts (M := M) e
  let d := identityDiffeomorph (M := M) e
  obtain ⟨O, hO, hc, hP⟩ := P.joint_C1 ε hε hw
  refine ⟨O, hO, hc, ?_⟩
  have hin : ContMDiff ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, F)))
      ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) 1
      (fun z : Control (ι := ι) × M => (z.1, d.symm z.2)) :=
    contMDiff_fst.prodMk ((d.symm.contMDiff.of_le (by simp)).comp contMDiff_snd)
  have hpre := hP.comp hin.contMDiffOn (show MapsTo
    (fun z : Control (ι := ι) × M => (z.1, d.symm z.2)) (O ×ˢ univ) (O ×ˢ univ)
    from fun _ hz => hz)
  exact (d.contMDiff.of_le (by simp)).comp_contMDiffOn hpre

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- Control rank is transported by the actual identity differential,
which is a linear equivalence. -/
theorem linearRechart_control_surjective (e : E ≃L[ℝ] F)
    (P : Maps (E := E) (ι := ι) T r) (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ P.window)
    (v : cube (ι := ι) ε) (x : M) :
    letI := charts (M := M) e;
    Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, F))
      (fun a => P.family ε a x) v.val) := by
  let := charts (M := M) e
  let d := identityDiffeomorph (M := M) e
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hcomp := mfderiv_comp v.val (d.contMDiffAt.mdifferentiableAt hn)
    (P.control_mdifferentiableAt ε hε hw v x)
  change Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, F))
    (d ∘ fun a => P.family ε a x) v.val)
  rw [hcomp]
  have hs : Function.Surjective
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) d (P.family ε v.val x)) := by
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe d hn]
    exact (d.mfderivToContinuousLinearEquiv hn _).surjective
  exact hs.comp (P.control_surjective ε hε hw v x)

/-- The recharted Maps record retains the literal maps, window and controls.
No joint-C¹ or submersion assumption is added. -/
def Maps.linearRechart (e : E ≃L[ℝ] F) (P : Maps (E := E) (ι := ι) T r)
    (hT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (calculus : LinearFractionalCalculus (T := T) e r) :
    letI := charts (M := M) e; Maps (E := F) (ι := ι) T r := by
  letI := charts (M := M) e
  exact {
    window := P.window
    window_positive := P.window_positive
    family := P.family
    atlas := P.atlas.linearRechart e
    constant := linearModelConstant e r * P.constant
    constant_positive := mul_pos (linearModelConstant_positive e r) P.constant_positive
    map_regular := fun ε hε hw v => calculus.regular _ (P.map_regular ε hε hw v)
    joint_C1 := linearRechart_joint_C1 e P
    control_surjective := linearRechart_control_surjective e P
    whitney_bound := fun ε hε hw v => by
      have hb := calculus.whitney _ P.atlas _ hT (P.map_regular ε hε hw v)
        (P.whitney_bound ε hε hw v)
      simpa only [mul_assoc] using hb }

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
