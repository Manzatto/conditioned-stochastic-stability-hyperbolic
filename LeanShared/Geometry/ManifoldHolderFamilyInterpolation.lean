module
public import LeanShared.Geometry.ManifoldHolderPowerInterpolation

/-! Quantitative continuity for actual manifold functions with uniformly
bounded higher Holder chart lifts. No regularity in the family index is used. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction BigOperators
namespace LeanShared.ManifoldHolderFamilyInterpolation
open ManifoldHolderCoordinateOperators ManifoldHolderCanonicalCoordinates
variable {E M J A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  (e : J→OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b a : ℝ} (hb : 0<b) (hb1 : b<1)

include atlas in
theorem exists_family_power_bound (hab:b<a) (region:V⊆S)
    (f:A→Regular e D openV hb hb1)
    (higher:A→D.indices→BoundedHolderSpace.graph E a)
    (agree:∀ p i y,BoundedHolderSpace.physical E a (higher p i) y =
      ChartLocalization.coordinate (e i) (D.cutoff i)
        (ManifoldSmoothHolderCore.physical e D openV hb hb1 (f p)) y)
    (L:D.indices→ℝ) (hL:∀i,0≤L i) (bound:∀ p i,‖higher p i‖≤L i) :
    ∃K:ℝ,0≤K ∧ ∀p q ε,0≤ε→
      (∀x,‖ManifoldSmoothHolderCore.physical e D openV hb hb1 (f p) x-
        ManifoldSmoothHolderCore.physical e D openV hb hb1 (f q) x‖≤ε)→
      dist (f p) (f q)≤K*ε^((a-b)/a) := by
  obtain ⟨K,hK,estimate⟩:=ManifoldHolderPowerInterpolation.exists_power_bound
    e D atlas openV hb hb1 hab (fun i=>2*L i) (fun i=>2*L i)
    (fun i=>mul_nonneg (by norm_num) (hL i))
    (fun i=>mul_nonneg (by norm_num) (hL i)) region
  refine ⟨K,hK,fun p q ε hε error=>?_⟩
  have difference : ∀i y,
      EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
        (coordinates e D atlas openV hb hb1 (f p-f q) i) y =
      BoundedHolderSpace.physical E a (higher p i-higher q i) y := by
    intro i y
    rw [localization_physical]
    simp only [map_sub,BoundedContinuousFunction.coe_sub,Pi.sub_apply]
    rw [agree p i y,agree q i y]
    unfold ChartLocalization.coordinate
    split_ifs <;> simp [mul_sub]
  have higherBound : ∀i,‖higher p i-higher q i‖≤2*L i := fun i=>
    (norm_sub_le _ _).trans (by linarith [bound p i,bound q i])
  rw [dist_eq_norm]
  apply estimate (f p-f q) ε hε
  · intro x
    simpa only [map_sub,BoundedContinuousFunction.coe_sub,Pi.sub_apply] using error x
  · intro i
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (by norm_num) (hL i))).mpr
    intro y
    rw [difference]
    exact ((BoundedHolderSpace.physical E a (higher p i-higher q i)).norm_coe_le_norm y).trans
      ((BoundedHolderSpace.physical_norm_le E a _).trans (higherBound i))
  · intro i x y
    rw [difference,difference]
    exact (BoundedHolderSpace.increment_bound E a (higher p i-higher q i) x y).trans
      (mul_le_mul_of_nonneg_right (higherBound i) (Real.rpow_nonneg dist_nonneg _))
local instance coordinateNormed {t:ℝ} (ht:0<t) (ht1:t<1) :
    NormedAddCommGroup (Coordinates e D openV ht ht1) := inferInstance
local instance coordinateSemi {t:ℝ} (ht:0<t) (ht1:t<1) :
    SeminormedAddCommGroup (Coordinates e D openV ht ht1) :=
  (coordinateNormed e D openV ht ht1).toSeminormedAddCommGroup
local instance coordinateScalar {t:ℝ} (ht:0<t) (ht1:t<1) :
    NormedSpace ℂ (Coordinates e D openV ht ht1) := inferInstance
local instance regularNormed {t:ℝ} (ht:0<t) (ht1:t<1) :
    NormedAddCommGroup (Regular e D openV ht ht1) := inferInstance
local instance regularSemi {t:ℝ} (ht:0<t) (ht1:t<1) :
    SeminormedAddCommGroup (Regular e D openV ht ht1) :=
  (regularNormed e D openV ht ht1).toSeminormedAddCommGroup
local instance regularScalar {t:ℝ} (ht:0<t) (ht1:t<1) :
    NormedSpace ℂ (Regular e D openV ht ht1) := inferInstance

include atlas in
theorem exists_family_power_bound_of_higher_space
    (ha:0<a) (ha1:a<1) (hab:b<a) (region:V⊆S)
    (f:A→Regular e D openV hb hb1)
    (higher:A→Regular e D openV ha ha1)
    (agree:∀p x,ManifoldSmoothHolderCore.physical e D openV ha ha1 (higher p) x =
      ManifoldSmoothHolderCore.physical e D openV hb hb1 (f p) x)
    {B:ℝ} (hB:0≤B) (bound:∀p,‖higher p‖≤B) :
    ∃K:ℝ,0≤K ∧ ∀p q ε,0≤ε→
      (∀x,‖ManifoldSmoothHolderCore.physical e D openV hb hb1 (f p) x-
        ManifoldSmoothHolderCore.physical e D openV hb hb1 (f q) x‖≤ε)→
      dist (f p) (f q)≤K*ε^((a-b)/a) := by
  apply exists_family_power_bound e D atlas openV hb hb1 hab region f
    (fun p i=>(coordinates e D atlas openV ha ha1 (higher p) i).val)
    ?_ (fun _=>‖coordinates e D atlas openV ha ha1‖*B)
    (fun _=>mul_nonneg (norm_nonneg _) hB) ?_
  · intro p i y
    change EuclideanSmoothHolderCore.physical _ ha ha1
      (coordinates e D atlas openV ha ha1 (higher p) i) y = _
    rw [localization_physical]
    have same : ManifoldSmoothHolderCore.physical e D openV ha ha1 (higher p) =
        ManifoldSmoothHolderCore.physical e D openV hb hb1 (f p) :=
      BoundedContinuousFunction.ext (agree p)
    rw [same]
  · intro p i
    exact (norm_le_pi_norm (coordinates e D atlas openV ha ha1 (higher p)) i).trans
      (((coordinates e D atlas openV ha ha1).le_opNorm (higher p)).trans
        (mul_le_mul_of_nonneg_left (bound p) (norm_nonneg _)))
end LeanShared.ManifoldHolderFamilyInterpolation
