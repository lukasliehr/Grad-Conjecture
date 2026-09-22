import ASG4RadialWeightMap

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def smoothRadialOrdinaryGraph (dimension : ℕ) (lower : ℝ) :
    SmoothRadialCore dimension →ₗ[ℝ] CollarH1 (ComplexEuclidean dimension) lower :=
  (collarH1Core (ComplexEuclidean dimension) lower).comp (SmoothRadialCore dimension).subtype

theorem smoothRadialOrdinaryGraph_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (core : SmoothRadialCore dimension) :
    ‖smoothRadialOrdinaryGraph dimension lower core‖ ≤
      Real.sqrt (1 / lower) * ‖weightedRadialCore dimension lower core‖ := by
  have value := weightedCurve_energy_lower dimension lower positive bounded core.val.val.1
  have slope := weightedCurve_energy_lower dimension lower positive bounded core.val.val.2
  have ordinary : ‖smoothRadialOrdinaryGraph dimension lower core‖ ^ 2 =
      (∫ radius in lower..1, ‖core.val.val.1 radius‖ ^ 2) +
        (∫ radius in lower..1, ‖core.val.val.2 radius‖ ^ 2) :=
    collarGraphLinear_norm_sq (ComplexEuclidean dimension) lower bounded core.val
  have stored : ‖weightedRadialCore dimension lower core‖ ^ 2 =
      ‖weightedCurveLinear dimension lower core.val.val.1‖ ^ 2 +
      ‖weightedCurveLinear dimension lower core.val.val.2‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    rfl
  have squared : ‖smoothRadialOrdinaryGraph dimension lower core‖ ^ 2 ≤
      (1 / lower) * ‖weightedRadialCore dimension lower core‖ ^ 2 := by
    rw [one_div_mul_eq_div, le_div_iff₀ positive, ordinary, stored]
    nlinarith [value, slope]
  have nonnegative : 0 ≤ 1 / lower := by positivity
  have rooted := Real.sqrt_le_sqrt squared
  simpa only [Real.sqrt_mul nonnegative, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using rooted

theorem weightedToOrdinary_exists (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    ∃ mapping : WeightedRadialH1 dimension lower →L[ℝ] CollarH1 (ComplexEuclidean dimension) lower,
      (∀ core, mapping (weightedRadialCoreInto dimension lower core) =
        collarH1Core (ComplexEuclidean dimension) lower core.val) ∧
      (∀ field, ‖mapping field‖ ≤ Real.sqrt (1 / lower) * ‖field‖) :=
by
  have nonnegative : 0 ≤ Real.sqrt (1 / lower) := Real.sqrt_nonneg _
  have estimate := smoothRadialOrdinaryGraph_bound dimension lower positive bounded
  have extension : ∃ mapping : (LinearMap.range (weightedRadialCore dimension lower)).topologicalClosure →L[ℝ]
      CollarH1 (ComplexEuclidean dimension) lower,
      (∀ core, mapping ⟨weightedRadialCore dimension lower core,
        Submodule.le_topologicalClosure _ ⟨core, rfl⟩⟩ = smoothRadialOrdinaryGraph dimension lower core) ∧
      (∀ field, ‖mapping field‖ ≤ Real.sqrt (1 / lower) * ‖field‖) := by
    with_reducible exact (collarRange_extension
      (C := SmoothRadialCore dimension) (F := WeightedRadialAmbient dimension lower)
      (T := CollarH1 (ComplexEuclidean dimension) lower) (weightedRadialCore dimension lower)
      (smoothRadialOrdinaryGraph dimension lower) (Real.sqrt (1 / lower)) nonnegative estimate)
  obtain ⟨mapping, coreLaw, bound⟩ := extension
  refine ⟨mapping, ?_, bound⟩
  intro core
  exact coreLaw core

/-- The same genuine derivative graph in ordinary dr coordinates. The
lower annulus radius makes this change of storage bounded. -/
def weightedToOrdinary (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    WeightedRadialH1 dimension lower →L[ℝ] CollarH1 (ComplexEuclidean dimension) lower :=
  (weightedToOrdinary_exists dimension lower positive bounded).choose

theorem weightedToOrdinary_core (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (core : SmoothRadialCore dimension) :
    weightedToOrdinary dimension lower positive bounded (weightedRadialCoreInto dimension lower core) =
      collarH1Core (ComplexEuclidean dimension) lower core.val :=
  (weightedToOrdinary_exists dimension lower positive bounded).choose_spec.1 core

theorem weightedRadialCoordinate_eq_sqrt (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (coordinate : Fin 2)
    (field : WeightedRadialH1 dimension lower) :
    weightedRadialCoordinate dimension lower coordinate field =
      radialSqrtMap dimension lower
        (collarH1Coordinate (ComplexEuclidean dimension) lower coordinate
          (weightedToOrdinary dimension lower positive bounded field)) := by
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq (weightedRadialCoordinate dimension lower coordinate).continuous
      ((radialSqrtMap dimension lower).continuous.comp
        ((collarH1Coordinate (ComplexEuclidean dimension) lower coordinate).continuous.comp
          (weightedToOrdinary dimension lower positive bounded).continuous))) _ field
  intro core
  simp only [Function.comp_apply]
  rw [weightedToOrdinary_core]
  fin_cases coordinate
  · change weightedCurveLinear dimension lower core.val.val.1 =
      radialSqrtMap dimension lower (collarContinuousL2 (ComplexEuclidean dimension) lower core.val.val.1)
    exact (radialSqrtMap_core dimension lower core.val.val.1).symm
  · change weightedCurveLinear dimension lower core.val.val.2 =
      radialSqrtMap dimension lower (collarContinuousL2 (ComplexEuclidean dimension) lower core.val.val.2)
    exact (radialSqrtMap_core dimension lower core.val.val.2).symm

/-- A completed AH10 radial source is determined by its actual weighted bulk
value. The derivative and either endpoint cannot vary independently. -/
theorem weightedRadial_value_injective (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    Function.Injective (weightedRadialCoordinate dimension lower 0) := by
  intro first second sameValue
  have ordinaryValue :
      collarH1Coordinate (ComplexEuclidean dimension) lower 0 (weightedToOrdinary dimension lower positive bounded first) =
      collarH1Coordinate (ComplexEuclidean dimension) lower 0 (weightedToOrdinary dimension lower positive bounded second) := by
    apply radialSqrtMap_injective dimension lower positive
    rw [← weightedRadialCoordinate_eq_sqrt, ← weightedRadialCoordinate_eq_sqrt, sameValue]
  have sameOrdinary := collarH1_value_injective lower bounded ordinaryValue
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  change weightedRadialCoordinate dimension lower coordinate first =
    weightedRadialCoordinate dimension lower coordinate second
  rw [weightedRadialCoordinate_eq_sqrt dimension lower positive bounded coordinate first,
    weightedRadialCoordinate_eq_sqrt dimension lower positive bounded coordinate second, sameOrdinary]

/-- The decoded ordinary coordinates satisfy the genuine weak derivative
identity inherited from GC20; the stored coordinates are sqrt(r) times them. -/
theorem weightedRadial_weak (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (field : WeightedRadialH1 dimension lower) :
    CollarWeakDerivative lower
      (collarH1Coordinate (ComplexEuclidean dimension) lower 0 (weightedToOrdinary dimension lower positive bounded field))
      (collarH1Coordinate (ComplexEuclidean dimension) lower 1 (weightedToOrdinary dimension lower positive bounded field)) :=
  collarH1_weak lower bounded _

end Grad.AnnularSourceGraph
