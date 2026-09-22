import AKF5ExactFullConjugatedPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

/-- A bounded polynomial reserve on both coordinates of the same field. -/
def physicalPairReserve (parameters : PhaseParameters) (reserve : ℕ) : PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  ((hilbertReserve parameters 1 reserve).comp (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1))).prod
    ((hilbertReserve parameters 1 reserve).comp (ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)))

theorem physicalPairReserve_coefficient (parameters : PhaseParameters) (reserve : ℕ)
    (field : PhysicalHilbertPair) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode (physicalPairReserve parameters reserve field) =
      frequencyReserveSymbol reserve mode • hilbertPairCoefficient mode field := rfl

theorem physicalPairReserve_same (parameters : PhaseParameters) (reserve : ℕ)
    (higher lower : PhysicalHilbertPair)
    (same : ∀ mode, hilbertPairCoefficient mode higher =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ) ^ reserve • hilbertPairCoefficient mode lower) :
    physicalPairReserve parameters reserve higher = lower := by
  apply Prod.ext
  · exact hilbertReserve_same parameters 1 reserve higher.1 lower.1 (fun mode => congrArg Prod.fst (same mode))
  · exact hilbertReserve_same parameters 1 reserve higher.2 lower.2 (fun mode => congrArg Prod.snd (same mode))

theorem rawUnknownSevenOperator_reserve (parameters : PhaseParameters) (reserve : ℕ) (radius : ℝ) :
    (rawUnknownSevenOperator parameters radius).comp (physicalPairReserve parameters reserve) =
      (hilbertReserve parameters 7 reserve).comp (rawUnknownSevenOperator parameters radius) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  change rawUnknownSevenOperator parameters radius (physicalPairReserve parameters reserve field) mode =
    hilbertReserve parameters 7 reserve (rawUnknownSevenOperator parameters radius field) mode
  rw [rawUnknownSevenOperator_point, physicalPairReserve_coefficient, hilbertReserve_apply,
    rawUnknownSevenOperator_point]
  exact (unknownSevenPointMap radius mode).map_smul _ _

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

theorem conjugatedSmoothResponsePairCurve_grade (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade radius) =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ) ^ grade • hilbertPairCoefficient mode
        (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core 0 radius) := by
  rw [conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade mode radius inside,
    originalSmoothResponsePairCurve_coefficient_grade,
    conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core 0 mode radius inside]
  rw [Complex.ofReal_pow]
  exact smul_comm _ _ _

theorem conjugatedSmoothResponsePairCurve_shift (grade reserve : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core (grade + reserve) radius) =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ) ^ reserve • hilbertPairCoefficient mode
        (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core grade radius) := by
  rw [conjugatedSmoothResponsePairCurve_grade parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core (grade + reserve) radius inside,
    conjugatedSmoothResponsePairCurve_grade parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade radius inside,
    pow_add, mul_smul]
  exact smul_comm _ _ _

theorem conjugatedSmoothResponsePairCurve_reserve (grade reserve : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    physicalPairReserve parameters reserve
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core (grade + reserve) radius) =
      conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade radius :=
  physicalPairReserve_same parameters reserve _ _
    (conjugatedSmoothResponsePairCurve_shift parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade reserve radius inside)

end Grad.AnnularWeightedSystem
