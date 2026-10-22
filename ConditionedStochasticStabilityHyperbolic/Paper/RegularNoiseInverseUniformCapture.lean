module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import LeanShared.Topology.CompactNearDiagonalContinuity
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseUniformWindow
import Mathlib.Tactic

/-! Uniform control of the ORIGINAL constructed inverse family via the
reference inverse's actual modulus. No linear inverse-noise rate is claimed. -/
public noncomputable section
open Set
open scoped NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]

theorem InverseFamily.exists_uniform_distance {T:M≃ₜM} {r:ℝ} {F:Maps (E:=E) (ι:=ι) T r}
    (J:InverseFamily F) {error:ℝ} (positive:0<error) :
    ∃η:NNReal,0<η ∧ η≤J.window ∧∀ε:NNReal,0<ε→ε≤η→∀a:cube (ι:=ι) ε,∀y:M,
      dist (J.map ε (a.val,y)) (T.symm y)<error :=by
  obtain ⟨η,hη,_window,bound⟩:=F.inverse_uniform_window error positive
  refine ⟨min η J.window,lt_min hη J.positive,min_le_right _ _,?_⟩
  intro ε hp hw a
  exact bound ε hp (hw.trans (min_le_left _ _)) a _
    (J.right ε hp (hw.trans (min_le_right _ _)) _
      (J.contains ε hp (hw.trans (min_le_right _ _)) a.property))

theorem InverseFamily.exists_uniform_target {T:M≃ₜM} {r:ℝ} {F:Maps (E:=E) (ι:=ι) T r}
    (J:InverseFamily F) (K U:Set M) (compact:IsCompact K) (openU:IsOpen U)
    (target:MapsTo T.symm K U) :
    ∃η:NNReal,0<η ∧ η≤J.window ∧∀ε:NNReal,0<ε→ε≤η→∀a:cube (ι:=ι) ε,
      MapsTo (fun y=>J.map ε (a.val,y)) K U :=by
  have compactImage:=compact.image T.symm.continuous
  have imageInside:T.symm '' K⊆U:=by rintro _ ⟨y,hy,rfl⟩;exact target hy
  obtain ⟨δ,hδ,neighborhood⟩:=LeanShared.CompactNearDiagonalContinuity.exists_radius
    _ U compactImage openU imageInside id continuousOn_id 1 zero_lt_one
  obtain ⟨η,hη,window,close⟩:=J.exists_uniform_distance hδ
  refine ⟨η,hη,window,?_⟩
  intro ε hp hw a y hy
  exact (neighborhood (T.symm y) (mem_image_of_mem _ hy) _
    (by simpa only [dist_comm] using close ε hp hw a y)).1
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
