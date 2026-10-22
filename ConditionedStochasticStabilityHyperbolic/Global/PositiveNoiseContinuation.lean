module

public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins

/-! A harmless continuation outside a proven positive-noise window.
Clipping the scale preserves the original family exactly near zero and never
increases its noise error. It supplies all-positive interfaces without
asserting smoothing for the original family at large noise. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseContinuation
open AbsorbingMarkovChains LeanShared ShiftedFiltrationGeometry

def scale (δ ε : NNReal) : NNReal := min ε δ

theorem scale_positive {δ ε : NNReal} (hδ : 0 < δ) (hε : 0 < ε) : 0 < scale δ ε :=
  lt_min hε hδ

theorem scale_le_window (δ ε : NNReal) : scale δ ε ≤ δ := min_le_right _ _
theorem scale_le_original (δ ε : NNReal) : scale δ ε ≤ ε := min_le_left _ _
theorem scale_eq {δ ε : NNReal} (h : ε ≤ δ) : scale δ ε = ε := min_eq_left h

theorem eventually_scale_eq {δ : NNReal} (hδ : 0 < δ) :
    ∀ᶠ ε : NNReal in 𝓝[>] 0, scale δ ε = ε := by
  filter_upwards [(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε
  exact scale_eq hε.le

def chain {X : Type*} [MeasurableSpace X] (C : NNReal → CanonicalChain X)
    (δ ε : NNReal) : CanonicalChain X := C (scale δ ε)

theorem strongFeller {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (C : NNReal → CanonicalChain X) (δ : NNReal) (hδ : 0 < δ)
    (sf : ∀ ε, 0 < ε → ε ≤ δ → HasStrongFellerKernel (C ε)) :
    ∀ ε, 0 < ε → HasStrongFellerKernel (chain C δ ε) :=
  fun ε hε => sf (scale δ ε) (scale_positive hδ hε) (scale_le_window δ ε)

theorem chain_eventually_eq {X : Type*} [MeasurableSpace X]
    (C : NNReal → CanonicalChain X) {δ : NNReal} (hδ : 0 < δ) :
    ∀ᶠ ε : NNReal in 𝓝[>] 0, chain C δ ε = C ε := by
  filter_upwards [eventually_scale_eq hδ] with ε hε
  exact congrArg C hε

variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]

/-- Ordinary geometry is required only in its original positive window. -/
structure WindowedGeometry
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
    (root : ∀ s, Fin ((terminal s).val + 1)) (C : NNReal → CanonicalChain X) (δ : NNReal) where
  strict_trapping : MapsTo T (closure A) A
  separation : ∀ i, Λ i ⊆ interior Aᶜ
  transitive : ∀ i : Fin ℓ, ControlledPlaqueClosure.forwardTransitiveOn T (Λ (D.index i))
  noise : NNReal → Measure Ω
  probability : ∀ ε, IsProbabilityMeasure (noise ε)
  open_positive : ∀ ε, 0 < ε → ε ≤ δ → (noise ε).IsOpenPosMeasure
  maps : NNReal → X × Ω → X
  measurable : ∀ ε, Measurable (maps ε)
  continuous : ∀ ε, 0 < ε → ε ≤ δ → Continuous (maps ε)
  potential : X → ℝ
  potential_measurable : Measurable potential
  R : ℝ
  R_positive : 0 < R
  weight_bound : ∀ x, Real.exp (potential x) ≤ R
  actual_model : ∀ ε, (C ε).killedTransition =
    (NoiseKernel.chain (noise ε) (maps ε) (measurable ε) Aᶜ hA.measurableSet.compl
      (fun x => Real.exp (potential x)) (Real.measurable_exp.comp potential_measurable)
      R R_positive weight_bound).killedTransition
  zero_control : Ω
  zero_map : ∀ ε, 0 < ε → ε ≤ δ → ∀ x, maps ε (x, zero_control) = T x
  radius : NNReal → ℝ
  radius_positive : ∀ ε, 0 < ε → ε ≤ δ → 0 < radius ε
  image_ball : ∀ ε, 0 < ε → ε ≤ δ → ∀ z ∈ interior Aᶜ, ∀ y ∈ interior Aᶜ,
    dist (T z) y < radius ε → ∃ a, maps ε (z, a) = y
  edge : Fin ℓ → Fin ℓ → Prop
  connections : ∀ i j, edge i j → ∃ z : X,
    (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index j), dist ((T : X → X)^[n + 1] z) y < r) ∧
    (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ (D.index i), dist ((T.symm : X → X)^[n] z) y < r)
  assignment : ∀ j : Fin ℓ, ∃ s : Fin t, ∃ i : Fin ((terminal s).val + 1),
    Λ (D.index j) = Λ (D.index (DerivedHG2Basins.originalIndex i)) ∧
      Relation.ReflTransGen (fun a b => edge (DerivedHG2Basins.originalIndex a)
        (DerivedHG2Basins.originalIndex b)) i (root s)

namespace WindowedGeometry
variable {T : X ≃ₜ X} {A : Set X} {hA : IsOpen A} {Λ : I → Set X} {ℓ : ℕ}
  {D : AdaptedSource T A Λ ℓ} {t : ℕ} {terminal : Fin t → Fin ℓ}
  {root : ∀ s, Fin ((terminal s).val + 1)} {C : NNReal → CanonicalChain X} {δ : NNReal}
  (g : WindowedGeometry (Ω := Ω) T A hA Λ ℓ D t terminal root C δ)

def continued (hδ : 0 < δ) : DerivedHG2Basins.GeometricSources (Ω := Ω)
    T A hA Λ ℓ D t terminal root (chain C δ) where
  strict_trapping := g.strict_trapping
  separation := g.separation
  transitive := g.transitive
  noise ε := g.noise (scale δ ε)
  probability ε := g.probability (scale δ ε)
  open_positive _ε hε := g.open_positive _ (scale_positive hδ hε) (scale_le_window _ _)
  maps ε := g.maps (scale δ ε)
  measurable ε := g.measurable (scale δ ε)
  continuous _ε hε := g.continuous _ (scale_positive hδ hε) (scale_le_window _ _)
  potential := g.potential
  potential_measurable := g.potential_measurable
  R := g.R
  R_positive := g.R_positive
  weight_bound := g.weight_bound
  actual_model ε := g.actual_model (scale δ ε)
  zero_control := g.zero_control
  zero_map _ε hε := g.zero_map _ (scale_positive hδ hε) (scale_le_window _ _)
  radius ε := g.radius (scale δ ε)
  radius_positive _ε hε := g.radius_positive _ (scale_positive hδ hε) (scale_le_window _ _)
  image_ball _ε hε := g.image_ball _ (scale_positive hδ hε) (scale_le_window _ _)
  edge := g.edge
  connections := g.connections
  assignment := g.assignment

omit [CompactSpace X] in
theorem continued_noise_bound (hδ : 0 < δ) (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ ε, 0 < ε → ε ≤ δ → ∀ x z,
      dist (g.maps ε (x, z)) (T x) ≤ c * (ε : ℝ)) :
    ∀ ε, 0 < ε → ∀ x z,
      dist ((g.continued hδ).maps ε (x, z)) (T x) ≤ c * (ε : ℝ) := by
  intro ε hε x z
  exact (bound _ (scale_positive hδ hε) (scale_le_window _ _) x z).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast scale_le_original δ ε) hc)

end WindowedGeometry
end ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseContinuation
