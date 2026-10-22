module
public import LeanShared.Analysis.LocalHolderProduct
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! Local Holder increments are preserved by an actual bounded bilinear
map. The local value bounds and resulting constant are constructed,
including for composition of derivative operators. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.LocalHolderBilinear
variable {E F G H:Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem norm_apply_le (L:F→L[ℝ]G→L[ℝ]H) (u:F) (v:G) :
    ‖L u v‖≤‖L‖*‖u‖*‖v‖ :=
  ((L u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg v))

theorem exists_bound (L:F→L[ℝ]G→L[ℝ]H) {f:E→F} {g:E→G} {x:E} {a C D:ℝ}
    (ha:0≤a) (hC:0≤C) (hD:0≤D) {U V:Set E} (hU:U∈𝓝 x) (hV:V∈𝓝 x)
    (hf:∀y∈U,∀z∈U,‖f y-f z‖≤C*‖y-z‖^a)
    (hg:∀y∈V,∀z∈V,‖g y-g z‖≤D*‖y-z‖^a) :
    ∃W:Set E,IsOpen W ∧ x∈W ∧ W⊆U∩V ∧∃A:ℝ,0≤A ∧
      ∀y∈W,∀z∈W,‖L (f y) (g y)-L (f z) (g z)‖≤A*‖y-z‖^a :=by
  obtain ⟨O,subO,openO,inO⟩:=mem_nhds_iff.mp (inter_mem hU hV)
  let W:=O∩Metric.ball x 1
  have inW:x∈W:=⟨inO,Metric.mem_ball_self zero_lt_one⟩
  have small (y:E) (hy:y∈W):‖y-x‖^a≤1:=
    Real.rpow_le_one (norm_nonneg _) (by
      simpa only [Metric.mem_ball,dist_eq_norm] using (show dist y x<1 from hy.2).le) ha
  have fvalue (y:E) (hy:y∈W):‖f y‖≤‖f x‖+C:=by
    have estimate:=(hf y (subO hy.1).1 x (mem_of_mem_nhds hU)).trans
      (mul_le_mul_of_nonneg_left (small y hy) hC)
    have triangle:=norm_sub_le (f y) (f x)
    have reverse:‖f y‖≤‖f y-f x‖+‖f x‖:=by
      simpa only [sub_add_cancel] using norm_add_le (f y-f x) (f x)
    linarith
  have gvalue (y:E) (hy:y∈W):‖g y‖≤‖g x‖+D:=by
    have estimate:=(hg y (subO hy.1).2 x (mem_of_mem_nhds hV)).trans
      (mul_le_mul_of_nonneg_left (small y hy) hD)
    have reverse:‖g y‖≤‖g y-g x‖+‖g x‖:=by
      simpa only [sub_add_cancel] using norm_add_le (g y-g x) (g x)
    linarith
  refine ⟨W,openO.inter Metric.isOpen_ball,inW,(fun y hy=>subO hy.1),
    ‖L‖*((‖f x‖+C)*D+C*(‖g x‖+D)),by positivity,?_⟩
  intro y hy z hz
  have split:L (f y) (g y)-L (f z) (g z)=L (f y) (g y-g z)+L (f y-f z) (g z):=by
    simp only [map_sub,sub_apply]
    abel
  rw [split]
  calc
    _ ≤ ‖L (f y) (g y-g z)‖+‖L (f y-f z) (g z)‖:=norm_add_le _ _
    _ ≤ (‖L‖*‖f y‖)*‖g y-g z‖+‖L‖*(‖f y-f z‖*‖g z‖):=
      add_le_add (norm_apply_le L _ _ ) ((norm_apply_le L _ _).trans_eq (by ring))
    _ ≤ (‖L‖*(‖f x‖+C))*(D*‖y-z‖^a)+‖L‖*((C*‖y-z‖^a)*(‖g x‖+D)):=by
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left (fvalue y hy) (norm_nonneg L))
          (hg y (subO hy.1).2 z (subO hz.1).2) (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul (hf y (subO hy.1).1 z (subO hz.1).1) (gvalue z hz)
            (norm_nonneg _) (by positivity)) (norm_nonneg L))
    _ = _:=by ring
end LeanShared.LocalHolderBilinear
