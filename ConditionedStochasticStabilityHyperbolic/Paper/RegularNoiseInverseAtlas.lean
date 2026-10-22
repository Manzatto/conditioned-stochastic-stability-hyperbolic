module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

/-! The original Whitney presentation constructs an ordinary finite atlas
for the inverse map by swapping charts and taking actual image patches. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Manifold Topology

def WhitneyAtlas.inverse
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] {T : M ≃ₜ M}
    (a : WhitneyAtlas (E := E) (T : M → M)) : WhitneyAtlas (E := E) (T.symm : M → M) where
  count := a.count
  source := a.target
  target := a.source
  source_smooth := a.target_smooth
  target_smooth := a.source_smooth
  patch := fun i => T '' a.patch i
  patch_open := fun i => T.isOpenMap _ (a.patch_open i)
  patch_cover := by rw [← image_iUnion,a.patch_cover,Set.image_univ_of_surjective T.surjective]
  patch_compact := fun i => by rw [← T.image_closure]; exact (a.patch_compact i).image T.continuous
  patch_source := fun i => by rw [← T.image_closure]; exact a.deterministic_target i
  deterministic_target := fun i => by
    rw [← T.image_closure]
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    simpa only [Homeomorph.symm_apply_apply] using a.patch_source i hx

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
