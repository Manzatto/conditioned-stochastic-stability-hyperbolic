module

public import LeanShared.Geometry.FractionalManifoldRegularity
public import LeanShared.Geometry.LinearRechartedIdentity
public import LeanShared.Analysis.LinearConjugateJets

/-! The original real-order regularity is preserved by the actual linear
change of manifold model, with every top-order Holder estimate transported. -/

public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
open LinearRechartedManifold
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem chartMap_linearRechart (e : E ≃L[ℝ] F) (f : M → M) (x : M) :
    let original := chartMap (E := E) (F := E) f x
    letI := charts (M := M) e
    chartMap (E := F) (F := F) f x = e ∘ original ∘ e.symm := by
  dsimp only
  let := charts (M := M) e
  simp only [chartMap, extChartAt, mfld_simps, Function.comp_def]
  rfl

/-- Both the integer differentiability and the actual fractional Holder jets
are carried through the same linear coordinate change. -/
theorem Regular.linearRechart {r : ℝ} {f : M → M}
    (hf : Regular (E := E) (F := E) r f) (e : E ≃L[ℝ] F) :
    letI := charts (M := M) e
    Regular (E := F) (F := F) r f := by
  let := charts (M := M) e
  refine ⟨hf.nonnegative, ?_, ?_⟩
  · have forward := (identity_forward (M := M) e).of_le
      (show (⌊r⌋₊ : ℕ∞ω) ≤ ∞ by simp)
    have backward := (identity_backward (M := M) e).of_le
      (show (⌊r⌋₊ : ℕ∞ω) ≤ ∞ by simp)
    simpa only [Function.comp_def, id_eq] using
      forward.comp (hf.differentiable.comp backward)
  · intro unequal x
    obtain ⟨U, openU, inU, inside, C, nonnegative, bound⟩ := hf.holder unequal x
    let α := r - (⌊r⌋₊ : ℝ)
    let B := ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ^ ⌊r⌋₊
    have hα : 0 ≤ α := sub_nonneg.mpr (Nat.floor_le hf.nonnegative)
    have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    refine ⟨e '' U, e.toHomeomorph.isOpenMap _ openU, ?_, ?_,
      B * C * ‖e.symm.toContinuousLinearMap‖ ^ α,
      mul_nonneg (mul_nonneg hB nonnegative) (Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
    · refine ⟨extChartAt (𝓘(ℝ, E)) x x, inU, ?_⟩
      simp only [extChartAt, mfld_simps]
      rfl
    · rintro _ ⟨u, hu, rfl⟩
      have old := inside hu
      simp only [chartDomain, extChartAt, mfld_simps] at old ⊢
      simpa only [chartAt_eq e, mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph,
        e.symm_apply_apply] using old
    · intro y hy z hz
      obtain ⟨u, hu, rfl⟩ := hy
      obtain ⟨v, hv, rfl⟩ := hz
      rw [chartMap_linearRechart]
      simp only [LinearConjugateJets.iteratedFDeriv_conjugate, e.symm_apply_apply,
        ← map_sub]
      calc
        ‖LinearConjugateJets.transport e ⌊r⌋₊
            (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := E) f x) u -
              iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := E) f x) v)‖
            ≤ B * ‖iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := E) f x) u -
              iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := E) f x) v‖ :=
          LinearConjugateJets.norm_transport_le e ⌊r⌋₊ _
        _ ≤ B * (C * ‖u - v‖ ^ α) := mul_le_mul_of_nonneg_left
          (bound u hu v hv) hB
        _ ≤ B * (C * (‖e.symm.toContinuousLinearMap‖ * ‖e u - e v‖) ^ α) := by
          gcongr
          have op := e.symm.toContinuousLinearMap.le_opNorm (e u - e v)
          simpa only [ContinuousLinearEquiv.coe_coe, map_sub, e.symm_apply_apply] using op
        _ = (B * C * ‖e.symm.toContinuousLinearMap‖ ^ α) * ‖e u - e v‖ ^ α := by
          rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
          ring
        _ = (B * C * ‖e.symm.toContinuousLinearMap‖ ^ α) * ‖e (u - v)‖ ^
            (r - (⌊r⌋₊ : ℝ)) := by rw [map_sub]

end LeanShared.FractionalManifoldRegularity
