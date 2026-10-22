module
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod

/-! Ambient Euclidean integration as integration over actual parallel
orthogonal affine leaves, with the canonical volume normalization. -/
public noncomputable section
open MeasureTheory Set
namespace LeanShared.OrthogonalFubini
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def split (P : Submodule ℝ E) : (P × Pᗮ) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 (P × Pᗮ)).trans P.orthogonalDecomposition.symm.toMeasurableEquiv

theorem split_apply (P : Submodule ℝ E) (z : P × Pᗮ) : split P z=(z.1:E)+(z.2:E) := by
  simp only [split,MeasurableEquiv.trans_apply,MeasurableEquiv.toLp_apply,
    LinearIsometryEquiv.coe_toMeasurableEquiv,Submodule.orthogonalDecomposition_symm_apply]
  rfl

theorem preserving (P : Submodule ℝ E) :
    MeasurePreserving (split P) (volume.prod volume) volume := by
  exact P.orthogonalDecomposition.symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp P Pᗮ)

theorem integral (P : Submodule ℝ E) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (integrable : Integrable f) :
    (∫ x, f x) = ∫ v : Pᗮ, ∫ u : P, f ((u:E)+(v:E)) := by
  have changeVariables := (preserving P).integral_comp' f
  have productIntegrable : Integrable (fun z : P × Pᗮ => f (split P z)) :=
    (preserving P).integrable_comp_emb (split P).measurableEmbedding |>.mpr integrable
  rw [← changeVariables,integral_prod_symm _ productIntegrable]
  simp only [split_apply]
end LeanShared.OrthogonalFubini
