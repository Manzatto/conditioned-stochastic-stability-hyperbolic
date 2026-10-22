module

public import LeanShared.Dynamics.ToralCatMapHyperbolicLift
public import LeanShared.Dynamics.CompactExpandingFlowMixing
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! Topological mixing for the actual toral cat map. Its unstable real
flow is dense by irrational-rotation density on the unit circle, and the
map expands that flow by its explicit eigenvalue. Compactness supplies
uniform hitting times. No hyperbolic or full-HL source is assumed. -/

public noncomputable section
namespace LeanShared.ToralCatMap
open Set Function

theorem irrational_unstable_slope : Irrational (expanding - 1) := by
  have irrational : Irrational (Real.sqrt 5) := (show Nat.Prime 5 by decide).irrational_sqrt
  have translated := (irrational.add_ratCast (1 : ℚ)).div_ratCast (show (2 : ℚ) ≠ 0 by norm_num)
  convert translated using 1
  simp only [Rat.cast_one, Rat.cast_ofNat]
  unfold expanding
  ring

@[expose] def unstableFlow : ℝ →+ Torus where
  toFun := fun t => quotient (t • unstableVector)
  map_zero' := by simp [quotient]
  map_add' := by intro s t; ext <;> simp [quotient, unstableVector, add_mul]

theorem continuous_unstableFlow : Continuous unstableFlow := by
  have first := (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_id.mul (continuous_const (y := expanding - 1)))
  have second := AddCircle.continuous_mk' (1 : ℝ)
  simpa [unstableFlow, quotient, unstableVector] using first.prodMk second

theorem dense_unstableFlow : DenseRange unstableFlow := by
  have denseCircle : DenseRange (fun n : ℤ => n • ((expanding - 1 : ℝ) : UnitAddCircle)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr
      (by simpa only [div_one] using irrational_unstable_slope)
  rintro ⟨a, b⟩
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective b
  let q₀ : UnitAddCircle := ↑(r * (expanding - 1))
  let embed : UnitAddCircle → Torus := fun u => (q₀ + u, (r : UnitAddCircle))
  have continuousEmbed : Continuous embed := by dsimp only [embed]; fun_prop
  have inImage : (a, (r : UnitAddCircle)) ∈ embed '' closure
      (range (fun n : ℤ => n • ((expanding - 1 : ℝ) : UnitAddCircle))) := by
    refine ⟨a - q₀, denseCircle _, ?_⟩
    simp [embed]
  have imageSubset : embed '' range
      (fun n : ℤ => n • ((expanding - 1 : ℝ) : UnitAddCircle)) ⊆ range unstableFlow := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨r + (n : ℝ), ?_⟩
    apply Prod.ext
    · change ((((r + (n : ℝ)) * (expanding - 1) : ℝ)) : UnitAddCircle) =
        ((r * (expanding - 1) : ℝ) : UnitAddCircle) +
          n • ((expanding - 1 : ℝ) : UnitAddCircle)
      rw [← AddCircle.coe_zsmul, ← AddCircle.coe_add]
      congr 1
      simp only [zsmul_eq_mul]
      ring
    · simp [unstableFlow, quotient, unstableVector, embed]
  exact closure_mono imageSubset
    (image_closure_subset_closure_image continuousEmbed inImage)

theorem homeomorph_add (x y : Torus) : homeomorph (x + y) = homeomorph x + homeomorph y := by
  ext <;> simp [homeomorph, equiv, map] <;> abel

theorem scales_unstableFlow (t : ℝ) : homeomorph (unstableFlow t) = unstableFlow (expanding * t) := by
  change map (quotient (t • unstableVector)) = quotient ((expanding * t) • unstableVector)
  rw [← quotient_map]
  congr 1
  change linear (t • unstableVector) = (expanding * t) • unstableVector
  rw [linear.map_smul]
  change t • map unstableVector = (expanding * t) • unstableVector
  rw [map_unstableVector, smul_smul, mul_comm]

/-- The concrete compact toral cat map satisfies the paper's literal
all-large-times open-set mixing condition on the full manifold. -/
theorem mixing : HyperbolicBasicSet.MixingOn homeomorph univ :=
  CompactExpandingFlowMixing.mixing unstableFlow continuous_unstableFlow dense_unstableFlow
    homeomorph homeomorph_add expanding expanding_gt_one scales_unstableFlow

end LeanShared.ToralCatMap
