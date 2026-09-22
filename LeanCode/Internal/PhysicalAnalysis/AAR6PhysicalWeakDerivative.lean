import AAR3FaithfulEnergyRealization
import AAR5ActualFirstRow
import ANR26OrdinaryRadialPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarPairing_test_add (lower : ℝ) (first second : C(ℝ, ℝ))
    (vector : ComplexEuclidean 1) (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarPairing lower (first + second) vector field =
      collarPairing lower first vector field + collarPairing lower second vector field := by
  have curves : collarTestCurve (first + second) vector =
      collarTestCurve first vector + collarTestCurve second vector := by
    apply ContinuousMap.ext
    intro radius
    exact add_smul (first radius) (second radius) vector
  change inner ℂ (collarContinuousL2 (ComplexEuclidean 1) lower (collarTestCurve (first + second) vector)) field =
    inner ℂ (collarContinuousL2 (ComplexEuclidean 1) lower (collarTestCurve first vector)) field +
    inner ℂ (collarContinuousL2 (ComplexEuclidean 1) lower (collarTestCurve second vector)) field
  rw [curves, map_add, inner_add_left]

/-- Product rule on the accepted genuine weak radial graph. -/
theorem collarWeakDerivative_scalar (lower : ℝ) (coefficient slope : C(ℝ, ℝ))
    (derivativeLaw : ∀ radius, HasDerivAt coefficient (slope radius) radius)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    CollarWeakDerivative lower (collarScalar 1 lower coefficient value)
      (collarScalar 1 lower slope value + collarScalar 1 lower coefficient derivative) := by
  intro test vector
  let auxiliary : CollarTest lower :=
    { value := test.value * coefficient
      derivative := test.derivative * coefficient + test.value * slope
      derivativeLaw := fun radius => (test.derivativeLaw radius).mul (derivativeLaw radius)
      lowerZero := by change test.value lower * coefficient lower = 0; rw [test.lowerZero, zero_mul]
      upperZero := by change test.value 1 * coefficient 1 = 0; rw [test.upperZero, zero_mul] }
  have law := weak auxiliary vector
  change collarPairing lower (test.value * coefficient) vector derivative =
    -collarPairing lower (test.derivative * coefficient + test.value * slope) vector value at law
  rw [collarPairing_test_add] at law
  rw [map_add, collarScalar_pairing, collarScalar_pairing, collarScalar_pairing, law]
  abel

def annularInversePhase (parameters : PhaseParameters) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => Real.exp (-radialPhase parameters radius cell),
    Real.continuous_exp.comp (radialPhase_smooth parameters cell).continuous.neg⟩

def annularInversePhaseSlope (parameters : PhaseParameters) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => -annularPhaseSlope parameters cell radius * annularInversePhase parameters cell radius,
    (annularPhaseSlope_continuous parameters cell).neg.mul (annularInversePhase parameters cell).continuous⟩

theorem annularInversePhase_hasDerivAt (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) :
    HasDerivAt (annularInversePhase parameters cell)
      (annularInversePhaseSlope parameters cell radius) radius := by
  change HasDerivAt (fun point => Real.exp (-radialPhase parameters point cell))
    (-annularPhaseSlope parameters cell radius * Real.exp (-radialPhase parameters radius cell)) radius
  rw [mul_comm (-annularPhaseSlope parameters cell radius)]
  exact (radialPhase_hasDerivAt parameters cell radius).neg.exp

def annularOrdinaryCoordinate (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : HighAnnularMode) (coordinate : Fin 2) :
    annularEnergySpace lower length positive →L[ℝ] CollarL2 (ComplexEuclidean 1) lower :=
  (collarH1Coordinate (ComplexEuclidean 1) lower coordinate).comp
    ((weightedToOrdinary 1 lower positive bounded).comp (annularModeRadialH1 lower length positive mode))

def annularPhysicalValue (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (mode : HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℝ] CollarL2 (ComplexEuclidean 1) lower :=
  ((collarScalar 1 lower (annularInversePhase parameters mode.val.2)).restrictScalars ℝ).comp
    (annularOrdinaryCoordinate lower length positive bounded mode 0)

def annularPhysicalSlope (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (mode : HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℝ] CollarL2 (ComplexEuclidean 1) lower :=
  ((collarScalar 1 lower (annularInversePhaseSlope parameters mode.val.2)).restrictScalars ℝ).comp
    (annularOrdinaryCoordinate lower length positive bounded mode 0) +
  ((collarScalar 1 lower (annularInversePhase parameters mode.val.2)).restrictScalars ℝ).comp
    (annularOrdinaryCoordinate lower length positive bounded mode 1)

/-- Genuine weak differentiation after removing the original curved phase.
This establishes regularity before identifying the retained physical rows. -/
theorem annularPhysicalValue_weak (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (mode : HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    CollarWeakDerivative lower
      (annularPhysicalValue parameters lower length positive bounded mode field)
      (annularPhysicalSlope parameters lower length positive bounded mode field) :=
  collarWeakDerivative_scalar lower (annularInversePhase parameters mode.val.2)
    (annularInversePhaseSlope parameters mode.val.2) (annularInversePhase_hasDerivAt parameters mode.val.2)
    _ _ (annularModeRadialH1_weak lower length positive bounded mode field)

end Grad.AnnularReconstruction
