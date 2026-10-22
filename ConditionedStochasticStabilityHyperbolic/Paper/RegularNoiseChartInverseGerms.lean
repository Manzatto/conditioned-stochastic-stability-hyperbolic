module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily

/-! Both literal inverse germ identities for the actual constructed inverse
noise family in arbitrary valid chart pairs. Partial chart inverses cancel
only on their genuine open source/target neighborhoods. -/
public noncomputable section
open Set Filter IsManifold
open scoped Manifold Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]

theorem InverseFamily.chart_inverse_germs {T:M≃ₜM} {r:ℝ} {F:Maps (E:=E) (ι:=ι) T r}
    (J:InverseFamily F) (ε:NNReal) (hp:0<ε) (hw:ε≤J.window) (a:cube (ι:=ι) ε)
    (c d:OpenPartialHomeomorph M E) (y:E) (inside:y∈d.target)
    (target:J.map ε (a.val,d.symm y)∈c.source) :
    let f:=d∘F.family ε a.val∘c.symm
    let g:=c∘(fun z=>J.map ε (a.val,z))∘d.symm
    (g∘f)=ᶠ[𝓝 (g y)]id ∧ (f∘g)=ᶠ[𝓝 y]id :=by
  let inverse:M→M:=fun z=>J.map ε (a.val,z)
  have continuousInverse:Continuous inverse:=(J.map_contMDiff ε hp hw a).continuous
  have continuousForward:Continuous (F.family ε a.val):=
    (F.map_regular ε hp (hw.trans J.window_le) a).differentiable.continuous
  have member:a.val∈J.domain ε:=J.contains ε hp hw a.property
  have nearInverse:(inverse∘d.symm) ⁻¹' c.source∈𝓝 y:=
    (continuousInverse.continuousAt.comp (d.continuousAt_symm inside)).preimage_mem_nhds
      (c.open_source.mem_nhds target)
  constructor
  · let x:=c (inverse (d.symm y))
    have sourceX:x∈c.target:=c.map_source target
    have forwardX:F.family ε a.val (c.symm x)∈d.source:=by
      rw [show c.symm x=inverse (d.symm y) from c.left_inv target]
      rw [J.right ε hp hw _ member]
      exact d.map_target inside
    have nearForward:(F.family ε a.val∘c.symm) ⁻¹' d.source∈𝓝 x:=
      (continuousForward.continuousAt.comp (c.continuousAt_symm sourceX)).preimage_mem_nhds
        (d.open_source.mem_nhds forwardX)
    filter_upwards [c.open_target.mem_nhds sourceX,nearForward] with z hz hz'
    change c (inverse (d.symm (d (F.family ε a.val (c.symm z)))))=z
    have targetZ:F.family ε a.val (c.symm z)∈d.source:=hz'
    dsimp only [inverse]
    rw [d.left_inv targetZ,J.left ε hp hw _ member,c.right_inv hz]
  · filter_upwards [nearInverse,d.open_target.mem_nhds inside] with z hz hz'
    change d (F.family ε a.val (c.symm (c (inverse (d.symm z)))))=z
    have targetZ:J.map ε (a.val,d.symm z)∈c.source:=hz
    dsimp only [inverse]
    rw [c.left_inv targetZ,J.right ε hp hw _ member,d.right_inv hz']
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
