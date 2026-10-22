module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Analysis.FractionalDerivativeBounds

/-! Actual fractional coordinate controls from the manuscript noise certificate.
The statements concern coordinate patches, without pretending that partial
chart expressions are globally differentiable on Euclidean space. Quantitative
composition/extension calculus can consume these ordinary derivative fields. -/

@[expose] public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

namespace WhitneyAtlas.Bound
variable {T : M → M} {r δ : ℝ} {f : M → M}
  {A : WhitneyAtlas (E := E) T}

omit [FiniteDimensional ℝ E] in
theorem coordinate_difference (b : A.Bound r f δ) (hr : r ≠ (⌊r⌋₊ : ℝ))
    (i : Fin A.count) :
    FractionalDerivativeBounds.Difference (A.coordinate f i) (A.coordinate T i)
      (A.coordinatePatch i) ⌊r⌋₊ (r - (⌊r⌋₊ : ℝ)) δ := by
  refine ⟨fun k hk x hx => b.derivatives i k hk x hx, ?_⟩
  intro x hx y hy
  have heq :
      (iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) x -
          iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) y) -
        (iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) x -
          iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) y) =
      (iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) x -
          iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) x) -
        (iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) y -
          iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) y) := by abel
  rw [heq]
  exact b.holder hr i x hx y hy

end WhitneyAtlas.Bound

namespace Maps
variable {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)

omit [FiniteDimensional ℝ E] in
theorem coordinate_difference (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (control : cube (ι := ι) ε) (hr : r ≠ (⌊r⌋₊ : ℝ)) (i : Fin F.atlas.count) :
    FractionalDerivativeBounds.Difference
      (F.atlas.coordinate (F.family ε control.val) i) (F.atlas.coordinate T i)
      (F.atlas.coordinatePatch i) ⌊r⌋₊ (r - (⌊r⌋₊ : ℝ)) (F.constant * (ε : ℝ)) := by
  have hd := (F.whitney_bound ε hε hwindow control).coordinate_difference hr i
  have hc : F.constant * ‖control.val‖ ≤ F.constant * (ε : ℝ) :=
    mul_le_mul_of_nonneg_left
      (NoiseCubeRescaling.cube_norm_le (ε : ℝ) ε.property control) F.constant_positive.le
  exact ⟨fun k hk x hx => (hd.derivatives k hk x hx).trans hc,
    fun x hx y hy => (hd.highest x hx y hy).trans
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (norm_nonneg _) _))⟩

omit [FiniteDimensional ℝ E] in
/-- Uniform local finite-C^r data retain the highest fractional increments.
Only deterministic coordinate bounds and the actual Whitney noise bound
are used. No continuity in the full top C^r norm is assumed. -/
theorem uniform_coordinate_estimates (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (control : cube (ι := ι) ε) (hr : r ≠ (⌊r⌋₊ : ℝ)) (i : Fin F.atlas.count)
    (B : ℝ)
    (hderivatives : ∀ k ≤ ⌊r⌋₊, ∀ x ∈ F.atlas.coordinatePatch i,
      ‖iteratedFDeriv ℝ k (F.atlas.coordinate T i) x‖ ≤ B)
    (hhighest : ∀ x ∈ F.atlas.coordinatePatch i, ∀ y ∈ F.atlas.coordinatePatch i,
      ‖iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate T i) x -
        iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate T i) y‖ ≤
        B * ‖x - y‖ ^ (r - (⌊r⌋₊ : ℝ))) :
    (∀ k ≤ ⌊r⌋₊, ∀ x ∈ F.atlas.coordinatePatch i,
      ‖iteratedFDeriv ℝ k (F.atlas.coordinate (F.family ε control.val) i) x‖ ≤
        B + F.constant * (ε : ℝ)) ∧
    ∀ x ∈ F.atlas.coordinatePatch i, ∀ y ∈ F.atlas.coordinatePatch i,
      ‖iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate (F.family ε control.val) i) x -
        iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate (F.family ε control.val) i) y‖ ≤
        (B + F.constant * (ε : ℝ)) * ‖x - y‖ ^ (r - (⌊r⌋₊ : ℝ)) := by
  have hd := F.coordinate_difference ε hε hwindow control hr i
  constructor
  · intro k hk x hx
    exact (norm_le_norm_sub_add _ _).trans
      ((add_le_add (hd.derivatives k hk x hx) (hderivatives k hk x hx)).trans_eq (add_comm _ _))
  · intro x hx y hy
    calc
      _ ≤ ‖(iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate (F.family ε control.val) i) x -
          iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate (F.family ε control.val) i) y) -
          (iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate T i) x -
          iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate T i) y)‖ +
          ‖iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate T i) x -
          iteratedFDeriv ℝ ⌊r⌋₊ (F.atlas.coordinate T i) y‖ := norm_le_norm_sub_add _ _
      _ ≤ (F.constant * (ε : ℝ)) * ‖x - y‖ ^ (r - (⌊r⌋₊ : ℝ)) +
          B * ‖x - y‖ ^ (r - (⌊r⌋₊ : ℝ)) :=
        add_le_add (hd.highest x hx y hy) (hhighest x hx y hy)
      _ = (B + F.constant * (ε : ℝ)) * ‖x - y‖ ^ (r - (⌊r⌋₊ : ℝ)) := by ring

end Maps
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
