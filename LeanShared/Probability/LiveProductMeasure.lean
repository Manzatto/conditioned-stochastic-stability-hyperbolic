module

public import LeanShared.Probability.LiveProductCoordinates
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Comap

/-! Restricting the original factor and leaving the auxiliary factor live
commutes with the literal closed-state product coordinates. -/

@[expose] public noncomputable section
open MeasureTheory Set
namespace LeanShared.LiveProductCoordinates
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- Actual restricted product measures become the product of the restricted
original measure and the fully live auxiliary measure. -/
theorem map_comap_product (K : Set X) (hK : MeasurableSet K)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    [SFinite (μ.comap (Subtype.val : K → X))] :
    ((μ.prod ν).comap (Subtype.val : ↥(K ×ˢ (univ : Set Y)) → X × Y)).map
      (liveProduct K) = (μ.comap (Subtype.val : K → X)).prod ν := by
  let j : K × Y → X × Y := Prod.map Subtype.val id
  have hj : MeasurableEmbedding j :=
    (MeasurableEmbedding.subtype_coe hK).prodMap MeasurableEmbedding.id
  apply hj.map_injective
  rw [Measure.map_map hj.measurable (liveProduct K).measurable]
  have hjcomp : j ∘ liveProduct K = (Subtype.val : ↥(K ×ˢ (univ : Set Y)) → X × Y) := rfl
  rw [hjcomp, map_comap_subtype_coe (hK.prod MeasurableSet.univ)]
  have hright : ((μ.comap (Subtype.val : K → X)).prod ν).map j =
      (μ.restrict K).prod ν := by
    rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id]
    rw [map_comap_subtype_coe hK, Measure.map_id]
  rw [hright]
  simpa only [Measure.restrict_univ] using (Measure.prod_restrict (μ := μ) (ν := ν) K univ).symm

end LeanShared.LiveProductCoordinates
