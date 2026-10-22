module
public import LeanShared.Dynamics.HyperbolicExpansivity
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.PressureInvariantSubtype
public import LeanShared.Dynamics.ExpansiveSeparatedCardinality
public import LeanShared.Dynamics.SeparatedSpanningSubset

/-! A finite separated spanning set on the actual ambient hyperbolic core. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff
open ThermodynamicDefinitions

theorem BasicData.exists_separated_spanning
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (n : ℕ) (ε : ℝ) (positiveε : 0 < ε) :
    ∃ s : Finset M, Separated T Λ n ε s ∧
      ∀ x ∈ Λ, ∃ y ∈ s, ∀ j < n,
        dist ((T : M → M)^[j] x) ((T : M → M)^[j] y) < ε := by
  classical
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let : Nonempty Λ := b.nonempty.to_subtype
  let : MeasurableSpace Λ := borel Λ
  let : BorelSpace Λ := ⟨rfl⟩
  have forwardS (x : Λ) : (S x).val = T x.val := rfl
  have backwardS (x : Λ) : (S.symm x).val = T.symm x.val := rfl
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  have expansiveS : ∀ x y : Λ, (∀ j : ℕ,
      dist ((S : Λ → Λ)^[j] x) ((S : Λ → Λ)^[j] y) ≤ c ∧
      dist ((S.symm : Λ → Λ)^[j] x) ((S.symm : Λ → Λ)^[j] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have small := close j
    change dist (((S : Λ → Λ)^[j] x).val) (((S : Λ → Λ)^[j] y).val) ≤ c ∧
      dist (((S.symm : Λ → Λ)^[j] x).val) (((S.symm : Λ → Λ)^[j] y).val) ≤ c at small
    simpa only [iterate_coe_restriction S forwardS, iterate_coe_restriction S.symm backwardS] using small
  obtain ⟨a, _, count⟩ := FiniteExpansiveWords.exists_uniform_card_bound S c positiveC expansiveS
  obtain ⟨p, bound⟩ := count ε positiveε
  obtain ⟨s, separated, spans⟩ := exists_separated_spanning_subset S univ n ε positiveε
    (a^(n+p)) (bound n)
  let ambient := s.image (fun x : Λ => x.val)
  have ambientSeparated : Separated T Λ n ε ambient := by
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact y.property
    intro x hx y hy different
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj, far⟩ := separated.2 u hu v hv (fun equal => different (congrArg Subtype.val equal))
    refine ⟨j, hj, ?_⟩
    change ε ≤ dist (((S : Λ → Λ)^[j] u).val) (((S : Λ → Λ)^[j] v).val) at far
    simpa only [iterate_coe_restriction S forwardS] using far
  refine ⟨ambient, ambientSeparated, ?_⟩
  intro x hx
  obtain ⟨y, hy, close⟩ := spans ⟨x,hx⟩ (mem_univ _)
  refine ⟨y.val, Finset.mem_image.mpr ⟨y,hy,rfl⟩, fun j hj => ?_⟩
  have small := close j hj
  change dist (((S : Λ → Λ)^[j] ⟨x,hx⟩).val) (((S : Λ → Λ)^[j] y).val) < ε at small
  simpa only [iterate_coe_restriction S forwardS] using small

end LeanShared.HyperbolicBasicSet
