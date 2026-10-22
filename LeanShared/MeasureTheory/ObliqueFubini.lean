module
public import LeanShared.MeasureTheory.OrthogonalFubini
public import Mathlib.MeasureTheory.Group.Prod

/-! Integration along actual parallel graphs of a continuous linear map.
The shear is measure preserving, so no determinant source is assumed. -/
public noncomputable section
open Set MeasureTheory Filter
namespace LeanShared.ObliqueFubini
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def shear (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) : (U × Uᗮ) ≃ᵐ (U × Uᗮ) where
  toFun z := (z.1,L z.1+z.2)
  invFun z := (z.1,z.2-L z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk ((L.continuous.measurable.comp measurable_fst).add measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (L.continuous.measurable.comp measurable_fst))

theorem shear_preserving (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) :
    MeasurePreserving (shear U L) (volume.prod volume) (volume.prod volume) := by
  exact (MeasurePreserving.id volume).skew_product
    ((L.continuous.measurable.comp measurable_fst).add measurable_snd)
    (Eventually.of_forall (fun u => map_add_left_eq_self volume (L u)))

@[expose] def split (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) : (U × Uᗮ) ≃ᵐ E :=
  (shear U L).trans (OrthogonalFubini.split U)

theorem split_apply (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (z : U × Uᗮ) :
    split U L z=(z.1:E)+(L z.1:E)+(z.2:E) := by
  change OrthogonalFubini.split U (z.1,L z.1+z.2)=_
  rw [OrthogonalFubini.split_apply]
  simp only [Submodule.coe_add,add_assoc]

theorem preserving (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) :
    MeasurePreserving (split U L) (volume.prod volume) volume :=
  (OrthogonalFubini.preserving U).comp (shear_preserving U L)

theorem integral (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (integrable : Integrable f) :
    (∫ x, f x) = ∫ v : Uᗮ, ∫ u : U, f ((u:E)+(L u:E)+(v:E)) := by
  have changeVariables := (preserving U L).integral_comp' f
  have productIntegrable : Integrable (fun z : U × Uᗮ => f (split U L z)) :=
    (preserving U L).integrable_comp_emb (split U L).measurableEmbedding |>.mpr integrable
  rw [← changeVariables,integral_prod_symm _ productIntegrable]
  simp only [split_apply]
end LeanShared.ObliqueFubini
