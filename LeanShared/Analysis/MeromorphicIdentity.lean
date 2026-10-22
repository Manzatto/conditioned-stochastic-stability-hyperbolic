module
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic

/-! A connected-domain identity principle for vector-valued meromorphic
functions at points where their actual values are continuous. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.MeromorphicIdentity
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem eq_of_eventuallyEq {f g : ℂ → Z} {S : Set ℂ}
    (mf : MeromorphicOn f S) (mg : MeromorphicOn g S)
    (connected : IsPreconnected S) {z₀ : ℂ} (member : z₀ ∈ S)
    (near : f =ᶠ[𝓝 z₀] g) {z : ℂ} (hz : z ∈ S)
    (cf : ContinuousAt f z) (cg : ContinuousAt g z) : f z = g z := by
  have difference : MeromorphicOn (f-g) S := mf.sub mg
  have zeroNear : ∀ᶠ w in 𝓝[≠] z₀, (f-g) w = 0 := by
    filter_upwards [near.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr hw
  have first : meromorphicOrderAt (f-g) z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr zeroNear
  have last := difference.meromorphicOrderAt_eq_top_of_isPreconnected connected member hz first
  have zeroLast : (f-g) =ᶠ[𝓝[≠] z] (fun _ => 0) :=
    meromorphicOrderAt_eq_top_iff.mp last
  have limitZero : Tendsto (f-g) (𝓝[≠] z) (𝓝 0) :=
    tendsto_const_nhds.congr' zeroLast.symm
  have limitValue : Tendsto (f-g) (𝓝[≠] z) (𝓝 ((f-g) z)) :=
    (cf.sub cg).mono_left nhdsWithin_le_nhds
  exact sub_eq_zero.mp (tendsto_nhds_unique limitValue limitZero)
end LeanShared.MeromorphicIdentity
