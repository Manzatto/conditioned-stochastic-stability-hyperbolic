module

public import LeanShared.Dynamics.ToralCatMapMixing
public import LeanShared.Dynamics.MixingDenseOrbit
public import LeanShared.Geometry.UnitAddCircleManifold
public import LeanShared.Geometry.LinearRechartedIdentity

/-! Actual smooth torus charts and a genuine Hilbert coordinate model for
the concrete mixing cat map. Both the map and its inverse are smooth;
the real quotient projection is smooth as well. The literal dense integer
orbit is obtained from the proved mixing theorem. -/

@[expose] public noncomputable section
open Set Function IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ToralCatMap

abbrev ProductModel := UnitAddCircleManifold.Model × UnitAddCircleManifold.Model
abbrev HilbertModel := WithLp 2 ProductModel

instance productChartedSpace : ChartedSpace ProductModel Torus :=
  prodChartedSpace UnitAddCircleManifold.Model UnitAddCircle UnitAddCircleManifold.Model UnitAddCircle

instance productManifold : IsManifold (𝓘(ℝ, ProductModel)) ∞ Torus := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, UnitAddCircleManifold.Model))
    (I' := 𝓘(ℝ, UnitAddCircleManifold.Model)) UnitAddCircle UnitAddCircle

def hilbertEquivalence : ProductModel ≃L[ℝ] HilbertModel :=
  LinearRechartedManifold.hilbertProductEquiv

instance hilbertChartedSpace : ChartedSpace HilbertModel Torus :=
  LinearRechartedManifold.charts (M := Torus) hilbertEquivalence

instance hilbertManifold : IsManifold (𝓘(ℝ, HilbertModel)) ∞ Torus :=
  LinearRechartedManifold.manifold (M := Torus) hilbertEquivalence

theorem smooth_map_product : ContMDiff (𝓘(ℝ, ProductModel)) (𝓘(ℝ, ProductModel)) ∞
    (map (G := UnitAddCircle)) := by
  unfold map
  rw [modelWithCornersSelf_prod]
  exact ((contMDiff_fst.add contMDiff_fst).add contMDiff_snd).prodMk
    (contMDiff_fst.add contMDiff_snd)

theorem smooth_inverse_product : ContMDiff (𝓘(ℝ, ProductModel)) (𝓘(ℝ, ProductModel)) ∞
    (inverse (G := UnitAddCircle)) := by
  unfold inverse
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_fst.sub contMDiff_snd).prodMk
    ((contMDiff_snd.add contMDiff_snd).sub contMDiff_fst)

theorem identity_to_hilbert : ContMDiff (𝓘(ℝ, ProductModel)) (𝓘(ℝ, HilbertModel)) ∞ (@id Torus) :=
  LinearRechartedManifold.identity_forward (M := Torus) hilbertEquivalence

theorem identity_from_hilbert : ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, ProductModel)) ∞ (@id Torus) :=
  LinearRechartedManifold.identity_backward (M := Torus) hilbertEquivalence

theorem smooth_map : ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ∞
    (map (G := UnitAddCircle)) := by
  simpa only [Function.comp_def, id_eq] using
    identity_to_hilbert.comp (smooth_map_product.comp identity_from_hilbert)

theorem smooth_inverse : ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ∞
    (inverse (G := UnitAddCircle)) := by
  simpa only [Function.comp_def, id_eq] using
    identity_to_hilbert.comp (smooth_inverse_product.comp identity_from_hilbert)

theorem smooth_homeomorph : ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ∞ homeomorph := by
  simpa [homeomorph, equiv] using smooth_map

theorem smooth_homeomorph_symm : ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ∞ homeomorph.symm := by
  simpa [homeomorph, equiv] using smooth_inverse

theorem smooth_quotient_product : ContMDiff (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ProductModel)) ∞ quotient := by
  rw [modelWithCornersSelf_prod (E := UnitAddCircleManifold.Model) (F := UnitAddCircleManifold.Model)]
  exact (UnitAddCircleManifold.smooth_projection.comp contDiff_fst.contMDiff).prodMk
    (UnitAddCircleManifold.smooth_projection.comp contDiff_snd.contMDiff)

theorem smooth_quotient : ContMDiff (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) ∞ quotient := by
  simpa only [Function.comp_def, id_eq] using identity_to_hilbert.comp smooth_quotient_product

theorem dense_orbit : ∃ x ∈ (univ : Set Torus),
    univ ⊆ closure (range (HyperbolicBasicSet.orbit homeomorph x)) :=
  mixing.exists_dense_orbit isCompact_univ univ_nonempty (by simp)

end LeanShared.ToralCatMap
