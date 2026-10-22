module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformControl
public import LeanShared.Geometry.ParametricSubmersionOpen

/-! Discharge the endpoint-openness classical source from the LITERAL C1
and control-rank hypotheses already present in RegularNoise.Maps. This uses
no noisy measure, spectral input, or pre-assumed image/covering estimate. -/
public section
open Set Filter IsManifold
open scoped Topology ContDiff Manifold NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

/-- Full control rank proves the entire joint endpoint-openness contract. -/
theorem proved_openCubeEndpointContract
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι] :
    OpenCubeEndpointContract (E := E) (M := M) (ι := ι) := by
  intro ε _hε H joint rank
  obtain ⟨O, hO, hcube, smooth⟩ := joint
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨⟨x, a⟩, ha, rfl⟩
  have hc : a ∈ LeanShared.NoiseCubeRescaling.cube (ι := ι) (ε : ℝ) := interior_subset ha.2
  have original : ContMDiffAt ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E)))
      (𝓘(ℝ, E)) 1 H (a, x) :=
    smooth.contMDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hcube hc, mem_univ x⟩)
  have swapped : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, Control (ι := ι))))
      (𝓘(ℝ, E)) 1 (fun z : M × Control (ι := ι) => H (z.2, z.1)) (x, a) :=
    original.comp (x, a) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have openMap := LeanShared.SubmersionOpen.endpoint_map_nhds_eq swapped (rank ⟨a, hc⟩ x)
  have neighbourhood : univ ×ˢ interior (LeanShared.NoiseCubeRescaling.cube (ι := ι) (ε : ℝ)) ∈
      𝓝 (x, a) := (isOpen_univ.prod isOpen_interior).mem_nhds ha
  have image := Filter.image_mem_map
    (m := fun z : M × Control (ι := ι) => (z.1, H (z.2, z.1))) neighbourhood
  rwa [openMap] at image
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
