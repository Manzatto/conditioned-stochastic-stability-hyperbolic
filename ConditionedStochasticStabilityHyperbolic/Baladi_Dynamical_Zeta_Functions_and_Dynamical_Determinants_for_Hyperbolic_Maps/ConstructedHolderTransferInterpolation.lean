module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderSingleTransfer
public import LeanShared.Geometry.ManifoldHolderFamilyInterpolation

/-! Actual weighted transfers of smooth inputs satisfy power interpolation
once their higher Holder operator norms are uniformly bounded. The same
physical weighted composition is used at both orders. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderTransferInterpolation
open LeanShared ConstructedHolderPhysicalModel ConstructedHolderSingleTransfer
variable {E M J A:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μE:Measure E) [μE.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)
  {g:M→ℝ} {q a:ℝ} (hbq:b<q)
  (hg:FractionalManifoldRegularity.Regular (E:=E) (F:=ℝ) q g)
  (support:tsupport g⊆V)
  (ha:0<a) (ha1:a<1) (hab:b<a) (haq:a<q)
  (maps:A→M→M) (regular:∀p,ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps p))

@[expose] def action (p:A) (c:SmoothSupportedManifoldCore.core (E:=E) V) :=
  transfer μE e D atlas openV region hb hb1 (maps p) (regular p) hbq hg support
    (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)

include μE atlas region hbq hg support ha ha1 hab haq maps regular in
omit [CompactSpace M] in
theorem exists_power_bound {B:ℝ} (hB:0≤B)
    (bound:∀p,‖transfer μE e D atlas openV region ha ha1 (maps p) (regular p) haq hg support‖≤B)
    (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    ∃K:ℝ,0≤K ∧ ∀p t ε,0≤ε→
      (∀x,‖view e D openV hb hb1
        (action μE e D atlas openV region hb hb1 hbq hg support maps regular p c) x-
        view e D openV hb hb1
        (action μE e D atlas openV region hb hb1 hbq hg support maps regular t c) x‖≤ε)→
      dist (action μE e D atlas openV region hb hb1 hbq hg support maps regular p c)
        (action μE e D atlas openV region hb hb1 hbq hg support maps regular t c)
        ≤K*ε^((a-b)/a) := by
  apply ManifoldHolderFamilyInterpolation.exists_family_power_bound_of_higher_space
    e D atlas openV hb hb1 ha ha1 hab region
    (fun p=>action μE e D atlas openV region hb hb1 hbq hg support maps regular p c)
    (fun p=>transfer μE e D atlas openV region ha ha1 (maps p) (regular p) haq hg support
      (ManifoldSmoothHolderCore.smooth e D atlas openV ha ha1 c))
    ?_ (mul_nonneg hB (norm_nonneg (ManifoldSmoothHolderCore.smooth e D atlas openV ha ha1 c))) ?_
  · intro p x
    change view e D openV ha ha1 _ x=view e D openV hb hb1 _ x
    rw [transfer_function]
    change (g x:ℂ)*view e D openV ha ha1
      (ManifoldSmoothHolderCore.smooth e D atlas openV ha ha1 c) (maps p x)=
      view e D openV hb hb1
        (transfer μE e D atlas openV region hb hb1 (maps p) (regular p) hbq hg support
          (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)) x
    rw [transfer_function]
    change (g x:ℂ)*ManifoldSmoothHolderCore.physical e D openV ha ha1
      (ManifoldSmoothHolderCore.smooth e D atlas openV ha ha1 c) (maps p x)=
      (g x:ℂ)*ManifoldSmoothHolderCore.physical e D openV hb hb1
        (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c) (maps p x)
    rw [ManifoldSmoothHolderCore.physical_smooth e D atlas openV ha ha1 region,
      ManifoldSmoothHolderCore.physical_smooth e D atlas openV hb hb1 region]
  · intro p
    exact ((transfer μE e D atlas openV region ha ha1 (maps p) (regular p) haq hg support).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (bound p) (norm_nonneg _))
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderTransferInterpolation
