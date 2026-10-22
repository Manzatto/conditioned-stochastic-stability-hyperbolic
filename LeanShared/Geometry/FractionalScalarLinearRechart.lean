module
public import LeanShared.Geometry.FractionalLinearRechartRegularity

/-! Real and complex scalar weights retain their exact finite real-order
regularity under the genuine change of manifold coordinate model. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
open LinearRechartedManifold
variable {E F G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M]

def scalarJetRechart (e : E ≃L[ℝ] F) (k : ℕ) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G) →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => F) G where
  toFun A := A.compContinuousLinearMap (fun _ => e.symm.toContinuousLinearMap)
  map_add' A B := by ext v; simp
  map_smul' c A := by ext v; simp

theorem norm_scalarJetRechart (e : E ≃L[ℝ] F) (k : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G) :
    ‖scalarJetRechart e k A‖ ≤ ‖e.symm.toContinuousLinearMap‖ ^ k * ‖A‖ := by
  have bound := A.norm_compContinuousLinearMap_le
    (fun _ : Fin k => e.symm.toContinuousLinearMap)
  simpa only [scalarJetRechart, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm] using bound

theorem iteratedFDeriv_scalarRechart (e : E ≃L[ℝ] F) (g : E → G) (k : ℕ) (x : F) :
    iteratedFDeriv ℝ k (g ∘ e.symm) x =
      scalarJetRechart e k (iteratedFDeriv ℝ k g (e.symm x)) := by
  have right := e.symm.iteratedFDerivWithin_comp_right g uniqueDiffOn_univ
    (mem_univ (e.symm x)) k
  simpa only [preimage_univ, iteratedFDerivWithin_univ, scalarJetRechart,
    LinearMap.coe_mk, AddHom.coe_mk] using right

theorem chartMap_scalarLinearRechart (e : E ≃L[ℝ] F) (g : M → G) (x : M) :
    let original := chartMap (E := E) (F := G) g x
    letI := charts (M := M) e
    chartMap (E := F) (F := G) g x = original ∘ e.symm := by
  dsimp only
  let := charts (M := M) e
  simp only [chartMap, extChartAt, mfld_simps, Function.comp_def]
  rfl

theorem Regular.scalarLinearRechart {r : ℝ} {g : M → G}
    (hg : Regular (E := E) (F := G) r g) (e : E ≃L[ℝ] F) :
    letI := charts (M := M) e
    Regular (E := F) (F := G) r g := by
  let := charts (M := M) e
  refine ⟨hg.nonnegative, ?_, ?_⟩
  · have backward := (identity_backward (M := M) e).of_le
      (show (⌊r⌋₊ : ℕ∞ω) ≤ ∞ by simp)
    simpa only [Function.comp_def, id_eq] using hg.differentiable.comp backward
  · intro unequal x
    obtain ⟨U, openU, inU, inside, C, nonnegative, bound⟩ := hg.holder unequal x
    let α := r - (⌊r⌋₊ : ℝ)
    let B := ‖e.symm.toContinuousLinearMap‖ ^ ⌊r⌋₊
    have hα : 0 ≤ α := sub_nonneg.mpr (Nat.floor_le hg.nonnegative)
    have hB : 0 ≤ B := pow_nonneg (norm_nonneg _) _
    refine ⟨e '' U, e.toHomeomorph.isOpenMap _ openU, ?_, ?_,
      B * C * ‖e.symm.toContinuousLinearMap‖ ^ α,
      mul_nonneg (mul_nonneg hB nonnegative) (Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
    · refine ⟨extChartAt (𝓘(ℝ,E)) x x, inU, ?_⟩
      simp only [extChartAt, mfld_simps]
      rfl
    · rintro _ ⟨v, hv, rfl⟩
      have old := inside hv
      simp only [chartDomain, extChartAt, mfld_simps] at old ⊢
      simpa only [chartAt_eq e, mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph,
        e.symm_apply_apply] using old
    · intro y hy z hz
      obtain ⟨v, hv, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hz
      rw [chartMap_scalarLinearRechart]
      simp only [iteratedFDeriv_scalarRechart, e.symm_apply_apply, ← map_sub]
      calc
        ‖scalarJetRechart e ⌊r⌋₊
            (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := G) g x) v -
              iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := G) g x) t)‖
            ≤ B * ‖iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := G) g x) v -
              iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := G) g x) t‖ :=
          norm_scalarJetRechart e ⌊r⌋₊ _
        _ ≤ B * (C * ‖v-t‖ ^ α) := mul_le_mul_of_nonneg_left (bound v hv t ht) hB
        _ ≤ B * (C * (‖e.symm.toContinuousLinearMap‖ * ‖e v-e t‖) ^ α) := by
          gcongr
          have op := e.symm.toContinuousLinearMap.le_opNorm (e v-e t)
          simpa only [ContinuousLinearEquiv.coe_coe, map_sub, e.symm_apply_apply] using op
        _ = (B * C * ‖e.symm.toContinuousLinearMap‖ ^ α) * ‖e v-e t‖ ^ α := by
          rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
          ring
        _ = (B * C * ‖e.symm.toContinuousLinearMap‖ ^ α) * ‖e (v-t)‖ ^
            (r-(⌊r⌋₊ : ℝ)) := by rw [map_sub]

end LeanShared.FractionalManifoldRegularity
