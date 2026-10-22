module
public import LeanShared.Geometry.FiniteSmoothReferenceJacobianFormula
public import LeanShared.Geometry.FiniteSmoothReferenceDensityBounds
public import LeanShared.Analysis.DeterminantHolderBound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform local Holder estimates for the actual computed Jacobian, from
ordinary inverse-coordinate derivative estimates. All reference-density and
determinant constants are constructed; no Jacobian Holder field is assumed. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold Metric
open scoped Topology Manifold ContDiff NNReal

private theorem product_increment {X : Type*} [PseudoMetricSpace X]
    (K : Set X) (f g : X → ℝ) (F G A B a : ℝ) (hF : 0 ≤ F)
    (vf : ∀ x ∈ K, ‖f x‖ ≤ F) (vg : ∀ x ∈ K, ‖g x‖ ≤ G)
    (hf : ∀ x ∈ K, ∀ y ∈ K, ‖f x-f y‖ ≤ A*dist x y^a)
    (hg : ∀ x ∈ K, ∀ y ∈ K, ‖g x-g y‖ ≤ B*dist x y^a)
    (x : X) (hx : x ∈ K) (y : X) (hy : y ∈ K) :
    ‖f x*g x-f y*g y‖ ≤ (F*B+A*G)*dist x y^a := by
  have split : f x*g x-f y*g y=f x*(g x-g y)+(f x-f y)*g y := by ring
  rw [split]
  calc
    _ ≤ ‖f x*(g x-g y)‖+‖(f x-f y)*g y‖ := norm_add_le _ _
    _ ≤ F*(B*dist x y^a)+(A*dist x y^a)*G := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul (vf x hx) (hg x hx y hy) (norm_nonneg _) hF)
        (mul_le_mul (hf x hx y hy) (vg y hy) (norm_nonneg _)
          ((norm_nonneg _).trans (hf x hx y hy)))
    _ = _ := by ring

set_option maxHeartbeats 2400000 in
theorem Data.jacobian_local_holder
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (s : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (family : P → M ≃ₜ M)
    (forward : ∀ p, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (family p))
    (inverse : ∀ p, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (family p).symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (K L : Set E) (compactK : IsCompact K) (convexK : Convex ℝ K) (sourceK : K ⊆ d.target)
    (compactL : IsCompact L) (convexL : Convex ℝ L) (sourceL : L ⊆ c.target)
    (diameter : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 1)
    (a M0 H0 : ℝ) (ha : a ≤ 1) (hH : 0 ≤ H0) (Lg : ℝ≥0)
    (capture : ∀ p x, x ∈ K → (family p).symm (d.symm x) ∈ c.source)
    (image : ∀ p x, x ∈ K → c ((family p).symm (d.symm x)) ∈ L)
    (lip : ∀ p, LipschitzOnWith Lg (c ∘ (family p).symm ∘ d.symm) K)
    (bounded : ∀ p x, x ∈ K → ‖fderiv ℝ (c ∘ (family p).symm ∘ d.symm) x‖ ≤ M0)
    (holder : ∀ p x, x ∈ K → ∀ y ∈ K,
      ‖fderiv ℝ (c ∘ (family p).symm ∘ d.symm) x-
        fderiv ℝ (c ∘ (family p).symm ∘ d.symm) y‖ ≤ H0*dist x y^a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p x, x ∈ K → ∀ y ∈ K,
      |s.jacobian (family p) (d.symm x)-s.jacobian (family p) (d.symm y)| ≤ C*dist x y^a := by
  obtain ⟨Lp,_,lipP,_⟩ := s.localDensity_lipschitzOn_compact c hc L compactL convexL sourceL
  obtain ⟨_,Lq,_,lipQ⟩ := s.localDensity_lipschitzOn_compact d hd K compactK convexK sourceK
  obtain ⟨Ap,boundP⟩ := compactL.exists_bound_of_continuousOn
    ((s.localDensity_continuousOn c hc).mono sourceL)
  obtain ⟨Aq,boundQ⟩ := compactK.exists_bound_of_continuousOn
    (((s.localDensity_inverse_contDiffOn d hd).continuousOn).mono sourceK)
  obtain ⟨Ad,boundD⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) M0).exists_bound_of_continuousOn
    SmoothDeterminant.contDiff.continuous.continuousOn
  obtain ⟨Ld,lipD⟩ := SmoothDeterminant.exists_lipschitz_bound (E := E) M0
  let Bp := max 0 Ap
  let Bq := max 0 Aq
  let Bd := max 0 Ad
  have hp : 0 ≤ Bp := le_max_left _ _
  have hq : 0 ≤ Bq := le_max_left _ _
  have hd' : 0 ≤ Bd := le_max_left _ _
  let C := (Bd*(Lp*Lg)+(Ld*H0)*Bp)*Bq+(Bd*Bp)*Lq
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro p x hx y hy
  let g := c ∘ (family p).symm ∘ d.symm
  let D := fun z => |(fderiv ℝ g z).det|
  let A := fun z => s.localDensity c (g z)
  let B := fun z => (s.localDensity d z)⁻¹
  have vD z (hz : z ∈ K) : ‖D z‖ ≤ Bd := by
    simpa only [D,Real.norm_eq_abs,abs_abs] using
      (boundD (fderiv ℝ g z) (by simpa only [mem_closedBall,dist_zero_right] using bounded p z hz)).trans
        (le_max_right 0 Ad)
  have vA z (hz : z ∈ K) : ‖A z‖ ≤ Bp :=
    (boundP _ (image p z hz)).trans (le_max_right _ _)
  have vB z (hz : z ∈ K) : ‖B z‖ ≤ Bq :=
    (boundQ z hz).trans (le_max_right _ _)
  have hD z (hz : z ∈ K) w (hw : w ∈ K) :
      ‖D z-D w‖ ≤ (Ld*H0)*dist z w^a := by
    change abs (abs (fderiv ℝ g z).det - abs (fderiv ℝ g w).det) ≤ _
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans
      ((lipD _ _ (bounded p z hz) (bounded p w hw)).trans
        ((mul_le_mul_of_nonneg_left (holder p z hz w hw) Ld.coe_nonneg).trans_eq (mul_assoc _ _ _).symm))
  have small z hz w hw : dist z w ≤ dist z w^a :=
    Real.self_le_rpow_of_le_one dist_nonneg (diameter z hz w hw) ha
  have hA z (hz : z ∈ K) w (hw : w ∈ K) :
      ‖A z-A w‖ ≤ (Lp*Lg)*dist z w^a := by
    have step := lipP.dist_le_mul (g z) (image p z hz) (g w) (image p w hw)
    have step' := step.trans (mul_le_mul_of_nonneg_left ((lip p).dist_le_mul z hz w hw) Lp.coe_nonneg)
    have result := (step'.trans_eq (mul_assoc (Lp : ℝ) (Lg : ℝ) (dist z w)).symm).trans
      (mul_le_mul_of_nonneg_left (small z hz w hw) (mul_nonneg Lp.coe_nonneg Lg.coe_nonneg))
    simpa only [dist_eq_norm,Real.norm_eq_abs] using result
  have hB z (hz : z ∈ K) w (hw : w ∈ K) : ‖B z-B w‖ ≤ Lq*dist z w^a := by
    have result := (lipQ.dist_le_mul z hz w hw).trans
      (mul_le_mul_of_nonneg_left (small z hz w hw) Lq.coe_nonneg)
    simpa only [Real.dist_eq,Real.norm_eq_abs,B] using result
  have numerator := product_increment K D A Bd Bp (Ld*H0) (Lp*Lg) a hd' vD vA hD hA
  have numeratorValue z (hz : z ∈ K) : ‖D z*A z‖ ≤ Bd*Bp := by
    rw [norm_mul]
    exact mul_le_mul (vD z hz) (vA z hz) (norm_nonneg _) hd'
  have result := product_increment K (fun z => D z*A z) B (Bd*Bp) Bq
    (Bd*(Lp*Lg)+(Ld*H0)*Bp) Lq a (mul_nonneg hd' hp) numeratorValue vB numerator hB x hx y hy
  have formula z (hz : z ∈ K) := s.jacobian_eq_inverse_chart_density μ (family p) (forward p) (inverse p)
    c d hc hd (d.symm z) (d.map_target (sourceK hz)) (capture p z hz)
  rw [formula x hx,formula y hy,d.right_inv (sourceK hx),d.right_inv (sourceK hy)]
  simpa only [div_eq_mul_inv,Real.norm_eq_abs,C,D,A,B,g,add_comm,Function.comp_apply] using result

end LeanShared.FiniteSmoothReferenceCharts
