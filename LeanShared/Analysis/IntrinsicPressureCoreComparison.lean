module
public import LeanShared.Analysis.IntrinsicLogJacobianCocycle
public import Mathlib.LinearAlgebra.Dimension.Finite

/-! Pointwise logarithmic pressure comparison for the actual intrinsic
coefficient. Positive unstable dimension proves positivity of the inverse
factor; the logarithmic bound then follows from the actual norm estimate. -/
@[expose] public noncomputable section
open Set
namespace LeanShared.IntrinsicPrincipalDensity
variable {G M : Type*} (F : G → M → M)
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))

omit [∀ x, FiniteDimensional ℝ (E x)] in
theorem inverseFactor_pos (word : List G) (x : M) (U : Submodule ℝ (E x))
    (hU : 0 < Module.finrank ℝ U) : 0 < inverseFactor F E D word x U := by
  have : Nontrivial U := Module.nontrivial_of_finrank_pos hU
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  have huval : u.val ≠ 0 := fun heq => hu (Subtype.ext heq)
  have hpos : 0 < ‖u.val‖ := norm_pos_iff.mpr huval
  have hbound := norm_le_inverseFactor_mul F E D word x U u.val u.property
  by_contra hnot
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot)
    (norm_nonneg (derivative F E D word x u.val))
  exact (not_lt_of_ge (hbound.trans hnonpos)) hpos

theorem log_density_le_orbitSum (g : M → ℝ) (K : Set M) (a : G)
    (hK : ∀ b, MapsTo (F b) K K) (hg : ∀ x ∈ K, 0 < g x)
    (stable unstable : (x : M) → Submodule ℝ (E x))
    (hinv : ∀ b x, x ∈ K → (unstable x).map (D b x).toLinearMap = unstable (F b x))
    (hdim : ∀ x ∈ K, 0 < Module.finrank ℝ (unstable x))
    (N : ℕ) (t s C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ) (x : M) (hx : x ∈ K)
    (hbound : max
      (stableFactor F E D (List.replicate N a) x (stable (orbit F (List.replicate N a) x)) ^ t)
      (inverseFactor F E D (List.replicate N a) x (unstable x) ^ (-s)) ≤ C * γ ^ N) :
    Real.log (density F E D g stable unstable N t s ((fun _ => a), x)) ≤
      ThermodynamicDefinitions.orbitSum (F a)
        (fun y => Real.log (g y) - Real.log (((D a y).toLinearMap.domRestrict (unstable y)).normDet)) N x +
      (Real.log C + (N : ℝ) * Real.log γ) := by
  have hpos : 0 < max
      (stableFactor F E D (List.replicate N a) x (stable (orbit F (List.replicate N a) x)) ^ t)
      (inverseFactor F E D (List.replicate N a) x (unstable x) ^ (-s)) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (inverseFactor_pos F E D _ x _ (hdim x hx)) _)
      (le_max_right _ _)
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_mul hC.ne' (pow_pos hγ N).ne', Real.log_pow] at hlog
  let scalar : List G → ℝ := fun word =>
    weight F g word x / unstableJacobian F E D word x (unstable x) *
      max (stableFactor F E D word x (stable (orbit F word x)) ^ t)
        (inverseFactor F E D word x (unstable x) ^ (-s))
  change Real.log (scalar (List.ofFn (fun _ : Fin N => a))) ≤ _
  rw [congrArg scalar (List.ofFn_const N a)]
  dsimp only [scalar]
  rw [Real.log_mul (div_pos (weight_pos F g K hK hg _ x hx)
      (unstableJacobian_pos F E D _ x (unstable x))).ne' hpos.ne',
    log_weight_div_jacobian F E D g K hK hg unstable hinv _ x hx,
    logPotentialSum_replicate]
  simpa only [add_comm] using add_le_add_left hlog
    (ThermodynamicDefinitions.orbitSum (F a)
      (fun y => Real.log (g y) - Real.log (((D a y).toLinearMap.domRestrict (unstable y)).normDet)) N x)

end LeanShared.IntrinsicPrincipalDensity
