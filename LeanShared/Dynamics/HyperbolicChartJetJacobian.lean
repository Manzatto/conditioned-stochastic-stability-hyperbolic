module
public import LeanShared.Dynamics.HyperbolicLocalParametricNativeJacobian
public import LeanShared.Geometry.ChartAffineJetFamily

/-! A literal finite first jet determines a continuous native Jacobian
functional on its genuine chart-validity domain. The functional uses the
original tangent metric and constructed extended unstable subspace. -/
@[expose] public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
open ChartAffineJetFamily
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}

def chartJetJacobian (a : h.NormedAdaptedProjection) (c d : OpenPartialHomeomorph M E)
    (q : Jet E) : ℝ :=
  ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun m => synthesis c d (q,m)) (c.symm q.1)).toLinearMap.domRestrict
    (a.unstable (c.symm q.1))).normDet

def validChartJets (a : h.NormedAdaptedProjection) (c d : OpenPartialHomeomorph M E) : Set (Jet E) :=
  {q | q.1 ∈ c.target ∧ q.2.1 ∈ d.target ∧ c.symm q.1 ∈ a.collar}

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem validChartJets_open (a : h.NormedAdaptedProjection) (c d : OpenPartialHomeomorph M E) :
    IsOpen (a.validChartJets c d) := by
  let S : Set (Jet E) := {q | q.1 ∈ c.target}
  have openS : IsOpen S := c.open_target.preimage continuous_fst
  have decoded : ContinuousOn (fun q : Jet E => c.symm q.1) S :=
    c.symm.continuousOn.comp continuous_fst.continuousOn (fun _ hq => hq)
  have collarOpen := decoded.isOpen_inter_preimage openS a.open_collar
  have outputOpen : IsOpen {q : Jet E | q.2.1 ∈ d.target} :=
    d.open_target.preimage (continuous_fst.comp continuous_snd)
  have same : a.validChartJets c d =
      (S ∩ (fun q : Jet E => c.symm q.1) ⁻¹' a.collar) ∩ {q : Jet E | q.2.1 ∈ d.target} := by
    ext q
    exact ⟨fun hq => ⟨⟨hq.1,hq.2.2⟩,hq.2.1⟩,
      fun hq => ⟨hq.1.1,hq.2,hq.1.2⟩⟩
  rw [same]
  exact collarOpen.inter outputOpen

theorem continuousOn_chartJetJacobian (a : h.NormedAdaptedProjection)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ContinuousOn (a.chartJetJacobian c d) (a.validChartJets c d) := by
  have decoded : ContinuousOn (fun q : Jet E => c.symm q.1) (a.validChartJets c d) :=
    c.symm.continuousOn.comp continuous_fst.continuousOn (fun _ hq => hq.1)
  have args := continuous_id.continuousOn.prodMk decoded
  apply (a.continuousOn_localParametricNativeJacobian (synthesis c d) (domain c d)
    (domain_open c d hc) ((synthesis_regular c d hc hd).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))).comp args
  intro q hq
  refine ⟨⟨c.map_target hq.1,?_⟩,mem_univ _,hq.2.2⟩
  change q.2.1 + q.2.2 (c (c.symm q.1)-q.1) ∈ d.target
  rw [c.right_inv hq.1,sub_self,map_zero,add_zero]
  exact hq.2.1

theorem tendsto_chartJetJacobian (a : h.NormedAdaptedProjection)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    {B : Type*} {l : Filter B} {q : B → Jet E} {q₀ : Jet E}
    (valid : q₀ ∈ a.validChartJets c d) (limit : Tendsto q l (𝓝 q₀)) :
    Tendsto (fun b => a.chartJetJacobian c d (q b)) l (𝓝 (a.chartJetJacobian c d q₀)) :=
  ((a.continuousOn_chartJetJacobian c d hc hd q₀ valid).continuousAt
    ((a.validChartJets_open c d).mem_nhds valid)).tendsto.comp limit

end LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
