module
public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! Exact comparison of restricted ambient measures and their actual subtype
realizations, with only the local almost-everywhere measurability needed for
maps defined on a compact control cube. -/
public section
namespace LeanShared.SubtypePushforward
open MeasureTheory Set

theorem map_comap_comp
    {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    (μ : Measure A) {L : Set A} (measurableL : MeasurableSet L)
    {f : A → Y} (measurableF : AEMeasurable f (μ.restrict L)) :
    (μ.comap (Subtype.val : L → A)).map (fun a => f a.val) = (μ.restrict L).map f := by
  have full : (μ.comap (Subtype.val : L → A)).map Subtype.val = μ.restrict L :=
    map_comap_subtype_coe measurableL μ
  have after : AEMeasurable f ((μ.comap (Subtype.val : L → A)).map Subtype.val) := by
    rw [full]
    exact measurableF
  rw [← full, AEMeasurable.map_map_of_aemeasurable after measurable_subtype_coe.aemeasurable]
  rfl

end LeanShared.SubtypePushforward
