module

public import ConditionedStochasticStabilityHyperbolic.Paper.AuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHG
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductSplitting
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedActualBasicProductEquilibrium
public import LeanShared.Dynamics.HyperbolicSplittingUniqueness
public import LeanShared.Geometry.HilbertProductSmoothMap

/-! Actual pressure preservation under auxiliary Anosov stabilization is
proved on every retained basic set. Positivity is used only there; no
absorbed-core logarithm or pressure assertion is introduced. -/
public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [CompactSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [CompactSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace (X × Y)] [Fintype κ]
local instance provedHGActualProductEquilibriumOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance provedHGActualProductEquilibriumOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance provedHGActualProductEquilibriumHilbertCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance provedHGActualProductEquilibriumHilbertManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A) (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)



theorem HG1.exponential_product_equilibrium
    (i : Fin D.count)
    (φ : X → ℝ) (hw : Continuous (fun x => Real.exp (φ x)))
    (μ : MeasureTheory.ProbabilityMeasure X)
    (state : ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x-Real.log ((D.basic i).hyperbolic.unstableJacobian x)) (D.core i) μ)
    (target : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr a.map) (D.core i ×ˢ univ)) :
    ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr a.map)
      (fun z => φ z.1-Real.log (target.unstableJacobian z)) (D.core i ×ˢ univ)
      (⟨(μ : MeasureTheory.Measure X).prod (a.equilibrium.state : MeasureTheory.Measure Y),inferInstance⟩ :
        MeasureTheory.ProbabilityMeasure (X × Y)) := by
  have hn : (1 : ℕ) ≤ ⌊h.r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using h.regularity_gt_one.le)
  have hy : (1 : ℕ) ≤ ⌊a.hl.r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using a.hl.regularity_gt_one.le)
  have forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T :=
    h.map_regular.differentiable.of_le (by exact_mod_cast hn)
  have inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm :=
    h.inverse_regular.differentiable.of_le (by exact_mod_cast hn)
  have auxForward : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 a.map :=
    a.hl.map_regular.differentiable.of_le (by exact_mod_cast hy)
  have auxInverse : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 a.map.symm :=
    a.hl.inverse_regular.differentiable.of_le (by exact_mod_cast hy)
  have productForward : ContMDiff (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) 1 (T.prodCongr a.map) :=
    HilbertProductDifferential.contMDiff_map T a.map forward auxForward
  have productInverse : ContMDiff (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) 1 (T.prodCongr a.map).symm :=
    HilbertProductDifferential.contMDiff_map T.symm a.map.symm inverse auxInverse
  have sameX : EqOn ((D.basic i).hyperbolic.potential (fun x=>Real.exp (φ x)))
      (fun x => φ x-Real.log ((D.basic i).hyperbolic.unstableJacobian x)) (D.core i) := by
    intro x hx
    simp only [HyperbolicData.potential,Real.log_exp]
  have actualState := (ThermodynamicDefinitions.isEquilibriumState_iff_of_eqOn
    (fun x hx => by rw [←(D.basic i).hyperbolic.invariant]; exact mem_image_of_mem _ hx) sameX μ).mpr state
  have made := BasicData.product_equilibrium_from_actual_data (D.basic i) a.hl.basic
    forward inverse auxForward auxInverse hw.continuousOn
    continuousOn_const (fun x _=>Real.exp_pos (φ x)) (fun _ _ => zero_lt_one)
    target (productForward.mdifferentiable (by norm_num))
    (productInverse.mdifferentiable (by norm_num)) μ a.equilibrium.state actualState a.equilibrium.equilibrium
  have sameProduct : EqOn (target.potential (fun z : X × Y => Real.exp (φ z.1)*(1 : ℝ)))
      (fun z => φ z.1-Real.log (target.unstableJacobian z)) (D.core i ×ˢ univ) := by
    intro z _
    simp only [HyperbolicData.potential,mul_one,Real.log_exp]
  exact (ThermodynamicDefinitions.isEquilibriumState_iff_of_eqOn
    (fun z hz => by rw [←target.invariant]; exact mem_image_of_mem _ hz) sameProduct _).mp made

end ConditionedStochasticStabilityHyperbolic.Paper
