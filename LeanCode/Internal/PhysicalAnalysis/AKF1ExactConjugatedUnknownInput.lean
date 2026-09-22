import AKB13GenuineConjugatedCoordinateDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution

/-- The accepted unknown seven operator acts on each Fourier coefficient
through this literal finite-dimensional linear map. -/
def unknownSevenPointMap (radius : ℝ) (mode : ℤ × ℤ) :
    (ComplexEuclidean 1 × ComplexEuclidean 1) →L[ℂ] ComplexEuclidean 7 :=
  let x := ContinuousLinearMap.fst ℂ (ComplexEuclidean 1) (ComplexEuclidean 1)
  let xi := ContinuousLinearMap.snd ℂ (ComplexEuclidean 1) (ComplexEuclidean 1)
  ((matrixUnit (0 : Fin 7) (0 : Fin 1)).comp (frequencyRatioSymbol none mode • x) +
    (radius : ℂ)⁻¹ • (matrixUnit (1 : Fin 7) (0 : Fin 1)).comp (frequencyRatioSymbol (some false) mode • xi)) +
    (matrixUnit (2 : Fin 7) (0 : Fin 1)).comp (frequencyRatioSymbol (some true) mode • xi) +
    (radius : ℂ)⁻¹ • (matrixUnit (3 : Fin 7) (0 : Fin 1)).comp (frequencyRatioSymbol none mode • xi)

theorem rawUnknownSevenOperator_point (parameters : PhaseParameters) (radius : ℝ)
    (field : PhysicalHilbertPair) (mode : ℤ × ℤ) :
    rawUnknownSevenOperator parameters radius field mode =
      unknownSevenPointMap radius mode (hilbertPairCoefficient mode field) := rfl

theorem rawUnknownSevenOperator_phase (parameters : PhaseParameters) (radius : ℝ)
    (first second : PhysicalHilbertPair) (mode : ℤ × ℤ) (scalar : ℝ)
    (same : hilbertPairCoefficient mode first = scalar • hilbertPairCoefficient mode second) :
    rawUnknownSevenOperator parameters radius first mode =
      scalar • rawUnknownSevenOperator parameters radius second mode := by
  rw [rawUnknownSevenOperator_point, rawUnknownSevenOperator_point, same]
  exact (unknownSevenPointMap radius mode).map_smul_of_tower scalar _

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The exact homogeneous seven packet of the SAME inverse, at its original
phase and polynomial grade, including both high and low Fourier sectors. -/
def conjugatedUnknownSevenCurve (grade : ℕ) (radius : ℝ) : CellL2 7 :=
  rawUnknownSevenOperator parameters radius
    (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core (grade + 2) radius)

theorem conjugatedUnknownSevenCurve_physical (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (mode : ℤ × ℤ) :
    conjugatedUnknownSevenCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode =
      Real.exp (radialPhase parameters radius mode.2) •
        sameUnknownSevenCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
          (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
          grade radius mode :=
  rawUnknownSevenOperator_phase parameters radius _ _ mode _
    (conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core (grade + 2) mode radius inside)

theorem conjugatedUnknownSevenCurve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedUnknownSevenCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade + 1) : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (homogeneousCoupledSevenInput parameters length lower lengthPositive positive
                (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)) radius mode) := by
  filter_upwards [sameUnknownCurve_actual parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) grade,
    ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  rw [conjugatedUnknownSevenCurve_physical parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core grade radius inside mode]
  change Real.exp (radialPhase parameters radius mode.2) •
    (rawUnknownSevenOperator parameters radius _ mode) = _
  rw [same mode]
  exact smul_comm _ _ _

end Grad.AnnularWeightedSystem
