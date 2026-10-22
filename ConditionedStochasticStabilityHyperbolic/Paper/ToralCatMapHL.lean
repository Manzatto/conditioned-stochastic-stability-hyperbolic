module

public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import LeanShared.Dynamics.ToralCatMapHyperbolic
public import LeanShared.Geometry.SmoothMapFractionalRegularity

/-! A concrete instance of the manuscript full-core HL hypothesis at
every finite real order r>1. It uses the actual mixing toral cat map,
constant weight one, genuine tangent hyperbolicity and proved fractional
regularity. No full-HL source is assumed. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Bundle Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap
open LeanShared

abbrev Model := LeanShared.ToralCatMap.HilbertModel
abbrev Torus := LeanShared.ToralCatMap.Torus

def hl (r : ℝ) (hr : 1 < r) : HL (E := Model) LeanShared.ToralCatMap.homeomorph
    (fun _ => 1) univ univ where
  r := r
  regularity_gt_one := hr
  map_regular := FractionalManifoldRegularity.regular_map_of_smooth
    LeanShared.ToralCatMap.smooth_homeomorph (zero_lt_one.trans hr).le
  inverse_regular := FractionalManifoldRegularity.regular_map_of_smooth
    LeanShared.ToralCatMap.smooth_homeomorph_symm (zero_lt_one.trans hr).le
  basic := LeanShared.ToralCatMap.basicData
  weight_regular := FractionalManifoldRegularity.regular_of_smooth contMDiff_const (by linarith)
  weight_nonnegative _ := zero_le_one
  weight_supported := subset_univ _
  weight_positive _ _ := zero_lt_one
  mixing := LeanShared.ToralCatMap.mixing

theorem hl_stable_positive (r : ℝ) (hr : 1 < r) (x : Torus) :
    0 < Module.finrank ℝ ((hl r hr).basic.hyperbolic.stable x) := by
  change 0 < Module.finrank ℝ (LeanShared.ToralCatMap.tangentStable x)
  rw [LeanShared.ToralCatMap.tangentStable_finrank]
  norm_num

theorem hl_unstable_positive (r : ℝ) (hr : 1 < r) (x : Torus) :
    0 < Module.finrank ℝ ((hl r hr).basic.hyperbolic.unstable x) := by
  change 0 < Module.finrank ℝ (LeanShared.ToralCatMap.tangentUnstable x)
  rw [LeanShared.ToralCatMap.tangentUnstable_finrank]
  norm_num

end ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap
