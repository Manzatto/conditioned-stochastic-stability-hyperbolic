module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.Order.Compact
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Uniform cone separation and fake-leaf secant slopes

All norms are those of one finite-dimensional real inner-product space.
Closed homogeneous cone separation gives one quantitative constant for every
admissible normal plane; the constant is not a background hypothesis.
-/

@[expose] public noncomputable section

open Set
open scoped RealInnerProductSpace

namespace LeanShared.ConeGraphGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Closed cone separation becomes a uniform lower bound on stable projection. -/
theorem exists_uniform_projection_lower_bound (U : Submodule ℝ E) {C : Set E}
    (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (htrans : ∀ v ∈ C, v ∈ U → v = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C, c * ‖v‖ ≤ ‖Uᗮ.starProjection v‖ := by
  have hcompact : IsCompact (C ∩ Metric.sphere (0 : E) 1) :=
    (isCompact_sphere (0 : E) 1).inter_left hclosed
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le'
    (Uᗮ.starProjection.continuous.norm.continuousOn) (a := (0 : ℝ)) (by
      intro v hv
      apply norm_pos_iff.mpr
      intro hp
      have hu : v ∈ U := by
        simpa only [Submodule.orthogonal_orthogonal] using
          (Uᗮ.starProjection_apply_eq_zero_iff.mp hp)
      have hz := htrans v hv.1 hu
      have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv.2
      simp [hz] at hn)
  refine ⟨c, hc, fun v hv => ?_⟩
  by_cases hz : v = 0
  · simp [hz]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have hv' : ‖v‖⁻¹ • v ∈ C ∩ Metric.sphere (0 : E) 1 := by
    refine ⟨hscale _ (inv_nonneg.mpr hn.le) v hv, ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ (ne_of_gt hn)]
  have hb := hbound _ hv'
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)] at hb
  have hm := mul_le_mul_of_nonneg_left hb hn.le
  simpa only [mul_inv_cancel_left₀ (ne_of_gt hn), mul_comm c ‖v‖] using hm

/-- Projection of an admissible normal plane to the stable reference space. -/
def planeProjection (U P : Submodule ℝ E) : P →ₗ[ℝ] Uᗮ :=
  Uᗮ.orthogonalProjectionOnto.toLinearMap.comp P.subtype

theorem planeProjection_injective (U P : Submodule ℝ E) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ v ∈ P, c * ‖v‖ ≤ ‖Uᗮ.starProjection v‖) :
    Function.Injective (planeProjection U P) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro v hv
    have hv0 : Uᗮ.starProjection (v : E) = 0 := by
      exact congrArg Subtype.val (show planeProjection U P v = 0 from hv)
    have hb := hbound (v : E) v.property
    rw [hv0, norm_zero] at hb
    have hn : ‖(v : E)‖ = 0 := by nlinarith [norm_nonneg (v : E)]
    exact Subtype.ext (norm_eq_zero.mp hn)
  · exact bot_le

theorem planeProjection_surjective (U P : Submodule ℝ E) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ v ∈ P, c * ‖v‖ ≤ ‖Uᗮ.starProjection v‖)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Uᗮ) :
    Function.Surjective (planeProjection U P) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (planeProjection_injective U P hc hbound)

/-- A common norm bound for lifts through every admissible normal plane. -/
theorem exists_plane_lift_bound (U P : Submodule ℝ E) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ v ∈ P, c * ‖v‖ ≤ ‖Uᗮ.starProjection v‖)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Uᗮ) (s : Uᗮ) :
    ∃ p : P, planeProjection U P p = s ∧ ‖(p : E)‖ ≤ c⁻¹ * ‖s‖ := by
  obtain ⟨p, hp⟩ := planeProjection_surjective U P hc hbound hdim s
  refine ⟨p, hp, ?_⟩
  have hb := hbound (p : E) p.property
  have heq : Uᗮ.starProjection (p : E) = (s : E) := congrArg Subtype.val hp
  rw [heq] at hb
  exact (le_inv_mul_iff₀ hc).mpr hb

/-- Approximate normality suffices, so an infimum-zero definition needs no minimizing plane. -/
theorem stable_projection_le_of_approximately_orthogonal (U P : Submodule ℝ E)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (hbound : ∀ v ∈ P, c * ‖v‖ ≤ ‖Uᗮ.starProjection v‖)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Uᗮ) (z : E)
    (hz : ∀ p ∈ P, |inner ℝ z p| ≤ ε * ‖z‖ * ‖p‖) :
    ‖Uᗮ.starProjection z‖ ≤ c⁻¹ * (‖U.starProjection z‖ + ε * ‖z‖) := by
  obtain ⟨p, hp, hpnorm⟩ := exists_plane_lift_bound U P hc hbound hdim
    (Uᗮ.orthogonalProjectionOnto z)
  have hpeq : Uᗮ.starProjection (p : E) = Uᗮ.starProjection z := congrArg Subtype.val hp
  have hs : inner ℝ (Uᗮ.starProjection z) (p : E) = ‖Uᗮ.starProjection z‖ ^ 2 := by
    rw [Uᗮ.inner_starProjection_left_eq_right, hpeq, real_inner_comm]
    simpa only [Submodule.starProjection_apply, Submodule.norm_coe, RCLike.re_to_real] using
      Uᗮ.re_inner_starProjection_eq_normSq z
  have heq : inner ℝ (U.starProjection z) (p : E) + ‖Uᗮ.starProjection z‖ ^ 2 =
      inner ℝ z (p : E) := by
    rw [← hs, ← inner_add_left, U.starProjection_add_starProjection_orthogonal]
  have hcs := abs_real_inner_le_norm (U.starProjection z) (p : E)
  have hsq : ‖Uᗮ.starProjection z‖ ^ 2 ≤
      (‖U.starProjection z‖ + ε * ‖z‖) * (c⁻¹ * ‖Uᗮ.starProjection z‖) := by
    have ha := hz (p : E) p.property
    have habs : ‖Uᗮ.starProjection z‖ ^ 2 ≤
        (‖U.starProjection z‖ + ε * ‖z‖) * ‖(p : E)‖ := by
      have ha1 := le_abs_self (inner ℝ z (p : E))
      have ha2 := neg_le_abs (inner ℝ (U.starProjection z) (p : E))
      nlinarith
    exact habs.trans (mul_le_mul_of_nonneg_left hpnorm (by positivity))
  by_cases hzero : ‖Uᗮ.starProjection z‖ = 0
  · rw [hzero]
    positivity
  have hpositive : 0 < ‖Uᗮ.starProjection z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  nlinarith [mul_comm (c⁻¹) (‖U.starProjection z‖ + ε * ‖z‖)]

/-- Orthogonality to a uniformly transverse normal plane controls every secant slope. -/
theorem stable_projection_le_of_orthogonal (U P : Submodule ℝ E) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ v ∈ P, c * ‖v‖ ≤ ‖Uᗮ.starProjection v‖)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Uᗮ) {z : E} (hz : z ∈ Pᗮ) :
    ‖Uᗮ.starProjection z‖ ≤ c⁻¹ * ‖U.starProjection z‖ := by
  simpa only [zero_mul, add_zero] using stable_projection_le_of_approximately_orthogonal
    U P hc (le_refl (0 : ℝ)) hbound hdim z (by
      intro p hp
      rw [real_inner_comm, hz p hp, abs_zero]
      simp)

/-- One derived constant works for all cone-contained normal planes and all secants. -/
theorem exists_uniform_secant_slope (U : Submodule ℝ E) {C : Set E}
    (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (htrans : ∀ v ∈ C, v ∈ U → v = 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ (P : Submodule ℝ E), (↑P : Set E) ⊆ C →
      Module.finrank ℝ P = Module.finrank ℝ Uᗮ →
      ∀ z ∈ Pᗮ, ‖Uᗮ.starProjection z‖ ≤ L * ‖U.starProjection z‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_uniform_projection_lower_bound U hclosed hscale htrans
  refine ⟨c⁻¹, inv_pos.mpr hc, fun P hPC hdim z hz => ?_⟩
  exact stable_projection_le_of_orthogonal U P hc (fun v hv => hbound v (hPC hv)) hdim hz

/-- Arbitrarily small normality errors imply the exact bound without attainment. -/
theorem stable_projection_le_of_arbitrarily_approximately_orthogonal
    (U : Submodule ℝ E) {C : Set E} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ v ∈ C, c * ‖v‖ ≤ ‖Uᗮ.starProjection v‖) (z : E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ P : Submodule ℝ E,
      (↑P : Set E) ⊆ C ∧ Module.finrank ℝ P = Module.finrank ℝ Uᗮ ∧
      ∀ p ∈ P, |inner ℝ z p| ≤ ε * ‖z‖ * ‖p‖) :
    ‖Uᗮ.starProjection z‖ ≤ c⁻¹ * ‖U.starProjection z‖ := by
  apply (le_inv_mul_iff₀ hc).mpr
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < ‖z‖ + 1 := by positivity
  have hδ : 0 < ε / (‖z‖ + 1) := div_pos hε hden
  obtain ⟨P, hPC, hdim, hp⟩ := happrox _ hδ
  have hb := stable_projection_le_of_approximately_orthogonal U P hc hδ.le
    (fun v hv => hbound v (hPC hv)) hdim z hp
  have hb' := mul_le_mul_of_nonneg_left hb hc.le
  rw [mul_inv_cancel_left₀ (ne_of_gt hc)] at hb'
  have heq : ε / (‖z‖ + 1) * (‖z‖ + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  have hsmall : ε / (‖z‖ + 1) * ‖z‖ ≤ ε := by nlinarith
  linarith

/-- The common cone constant also covers the manuscript's infimum-zero formulation. -/
theorem exists_uniform_approximate_secant_slope (U : Submodule ℝ E) {C : Set E}
    (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (htrans : ∀ v ∈ C, v ∈ U → v = 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ z : E,
      (∀ ε : ℝ, 0 < ε → ∃ P : Submodule ℝ E,
        (↑P : Set E) ⊆ C ∧ Module.finrank ℝ P = Module.finrank ℝ Uᗮ ∧
        ∀ p ∈ P, |inner ℝ z p| ≤ ε * ‖z‖ * ‖p‖) →
      ‖Uᗮ.starProjection z‖ ≤ L * ‖U.starProjection z‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_uniform_projection_lower_bound U hclosed hscale htrans
  exact ⟨c⁻¹, inv_pos.mpr hc, fun z hz =>
    stable_projection_le_of_arbitrarily_approximately_orthogonal U hc hbound z hz⟩

omit [FiniteDimensional ℝ E] in
/-- Because a real plane contains both signs, one-sided normalized inner-product
bounds imply the absolute estimate used by approximate normality. -/
theorem absolute_inner_bound_of_normalized_upper (P : Submodule ℝ E) (z : E)
    {ε : ℝ}
    (hupper : ∀ p ∈ P, ‖p‖ = 1 → inner ℝ (‖z‖⁻¹ • z) p ≤ ε) :
    ∀ p ∈ P, |inner ℝ z p| ≤ ε * ‖z‖ * ‖p‖ := by
  intro p hp
  by_cases hz : z = 0
  · simp [hz]
  by_cases hp0 : p = 0
  · simp [hp0]
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnp : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  let q := ‖p‖⁻¹ • p
  have hqP : q ∈ P := P.smul_mem _ hp
  have hqnorm : ‖q‖ = 1 := by
    simp only [q, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hnp.le), inv_mul_cancel₀ (ne_of_gt hnp)]
  have hu := hupper q hqP hqnorm
  have hl := hupper (-q) (P.neg_mem hqP) (by simpa only [norm_neg] using hqnorm)
  rw [inner_neg_right] at hl
  have habs : |inner ℝ (‖z‖⁻¹ • z) q| ≤ ε := abs_le.mpr ⟨by linarith, hu⟩
  simp only [q, real_inner_smul_left, real_inner_smul_right, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hnz.le), abs_of_nonneg (inv_nonneg.mpr hnp.le)] at habs
  have hm := mul_le_mul_of_nonneg_left habs (mul_nonneg hnz.le hnp.le)
  have heq : ‖z‖ * ‖p‖ * (‖p‖⁻¹ * (‖z‖⁻¹ * |inner ℝ z p|)) = |inner ℝ z p| := by
    field_simp
  rw [heq] at hm
  nlinarith

/-- Secant slope bounds make projection to the unstable reference space injective,
with a quantitative bound on its inverse over its image. -/
theorem norm_le_projection_of_slope (U : Submodule ℝ E) {L : ℝ}
    (z : E) (hslope : ‖Uᗮ.starProjection z‖ ≤ L * ‖U.starProjection z‖) :
    ‖z‖ ≤ (1 + L) * ‖U.starProjection z‖ := by
  calc
    ‖z‖ = ‖U.starProjection z + Uᗮ.starProjection z‖ := by
      rw [U.starProjection_add_starProjection_orthogonal]
    _ ≤ ‖U.starProjection z‖ + ‖Uᗮ.starProjection z‖ := norm_add_le _ _
    _ ≤ (1 + L) * ‖U.starProjection z‖ := by nlinarith

theorem leafProjection_antilipschitz (U : Submodule ℝ E) {Γ : Set E} {L : ℝ}
    (hL : 0 ≤ L)
    (hslope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x - y)‖ ≤ L * ‖U.starProjection (x - y)‖) :
    AntilipschitzWith (Real.toNNReal (1 + L))
      (fun x : Γ => U.orthogonalProjectionOnto (x : E)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  rw [Real.coe_toNNReal (1 + L) (by positivity)]
  simpa only [Subtype.dist_eq, dist_eq_norm, ← map_sub, Submodule.starProjection_apply,
    Submodule.norm_coe] using norm_le_projection_of_slope U ((x : E) - y)
      (hslope x x.property y y.property)

/-- An intrinsic orthogonal graph, using the ambient Euclidean norm. -/
def graphPoint (U : Submodule ℝ E) (h : U → Uᗮ) (u : U) : E := (u : E) + (h u : E)

@[simp] theorem unstable_graphPoint (U : Submodule ℝ E) (h : U → Uᗮ) (u : U) :
    U.starProjection (graphPoint U h u) = (u : E) := by
  rw [graphPoint, map_add, Submodule.starProjection_eq_self_iff.mpr u.property,
    (U.starProjection_apply_eq_zero_iff).mpr (h u).property, add_zero]

@[simp] theorem stable_graphPoint (U : Submodule ℝ E) (h : U → Uᗮ) (u : U) :
    Uᗮ.starProjection (graphPoint U h u) = (h u : E) := by
  rw [graphPoint, map_add,
    (Uᗮ.starProjection_apply_eq_zero_iff).mpr (U.le_orthogonal_orthogonal u.property),
    Submodule.starProjection_eq_self_iff.mpr (h u).property, zero_add]

/-- Orthogonal graph coordinates never exceed the true ambient Euclidean norm. -/
theorem parameter_norm_le_graphPoint (U : Submodule ℝ E) (h : U → Uᗮ) (u : U) :
    ‖u‖ ≤ ‖graphPoint U h u‖ := by
  simpa only [unstable_graphPoint, Submodule.norm_coe] using
    U.norm_starProjection_apply_le (graphPoint U h u)

theorem graphPoint_injective (U : Submodule ℝ E) (h : U → Uᗮ) :
    Function.Injective (graphPoint U h) := by
  intro u v huv
  apply Subtype.ext
  simpa only [unstable_graphPoint] using congrArg U.starProjection huv

/-- The slope estimate becomes a true Lipschitz estimate for an orthogonal graph. -/
theorem graph_lipschitz_of_secant_slope (U : Submodule ℝ E) (h : U → Uᗮ)
    {L : ℝ} (hL : 0 ≤ L)
    (hslope : ∀ u v : U,
      ‖Uᗮ.starProjection (graphPoint U h u - graphPoint U h v)‖ ≤
        L * ‖U.starProjection (graphPoint U h u - graphPoint U h v)‖) :
    LipschitzWith (Real.toNNReal L) h := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.coe_toNNReal L hL]
  simpa only [dist_eq_norm, map_sub, stable_graphPoint, unstable_graphPoint,
    ← Submodule.coe_sub, Submodule.norm_coe] using hslope u v

/-- The true derivative bound needed by the Gram-Jacobian density estimate. -/
theorem graph_derivative_norm_le (U : Submodule ℝ E) (h : U → Uᗮ)
    {L : ℝ} (hL : 0 ≤ L)
    (hslope : ∀ u v : U,
      ‖Uᗮ.starProjection (graphPoint U h u - graphPoint U h v)‖ ≤
        L * ‖U.starProjection (graphPoint U h u - graphPoint U h v)‖) (u : U) :
    ‖fderiv ℝ h u‖ ≤ L := by
  simpa only [Real.coe_toNNReal L hL] using norm_fderiv_le_of_lipschitz ℝ
    (graph_lipschitz_of_secant_slope U h hL hslope) (x₀ := u)

/-- One constant derived from transverse cones bounds the actual derivatives of
every admissible intrinsic graph, including approximate-normality leaves. -/
theorem exists_uniform_graph_derivative_bound (U : Submodule ℝ E)
    {Cplus Cminus : Set E} (hclosed : IsClosed Cplus)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ Cplus, r • v ∈ Cplus)
    (hcones : ∀ v ∈ Cplus, v ∈ Cminus → v = 0)
    (hU : (↑U : Set E) ⊆ Cminus) :
    ∃ L : ℝ, 0 < L ∧ ∀ h : U → Uᗮ,
      (∀ u v : U, ∀ ε : ℝ, 0 < ε → ∃ P : Submodule ℝ E,
        (↑P : Set E) ⊆ Cplus ∧ Module.finrank ℝ P = Module.finrank ℝ Uᗮ ∧
        ∀ p ∈ P, |inner ℝ (graphPoint U h u - graphPoint U h v) p| ≤
          ε * ‖graphPoint U h u - graphPoint U h v‖ * ‖p‖) →
      LipschitzWith (Real.toNNReal L) h ∧ ∀ u : U, ‖fderiv ℝ h u‖ ≤ L := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_approximate_secant_slope U hclosed hscale
    (fun v hv hu => hcones v hv (hU hu))
  refine ⟨L, hL, fun h hh => ?_⟩
  have hslope : ∀ u v : U,
      ‖Uᗮ.starProjection (graphPoint U h u - graphPoint U h v)‖ ≤
        L * ‖U.starProjection (graphPoint U h u - graphPoint U h v)‖ :=
    fun u v => hbound _ (hh u v)
  exact ⟨graph_lipschitz_of_secant_slope U h hL.le hslope,
    graph_derivative_norm_le U h hL.le hslope⟩

end LeanShared.ConeGraphGeometry
