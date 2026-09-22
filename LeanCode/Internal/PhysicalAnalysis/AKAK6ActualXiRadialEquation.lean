import AKAK4LiteralFullRadialCoefficients
import AKAK5ScalarRadialEquationSynthesis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness

private theorem xiPhysicalRHS_combine (mode : ℤ × ℤ)
    (physical original : ComplexEuclidean 1 × ComplexEuclidean 1)
    (j f total projected target : ComplexEuclidean 1)
    (physicalLaw : physical = (if mode.1 = 0 then (0 : ℂ) else 1) • original)
    (originalLaw : original.2 = (if mode.1 = 0 then (0 : ℂ) else 1) • (j+f))
    (totalLaw : total = j+f)
    (projectedLaw : projected = if mode.1 = 0 then 0 else total)
    (targetLaw : target = (annularFrequency mode.1 mode.2 : ℂ)^0 • projected) :
    physical.2 = target := by
  rw [physicalLaw,targetLaw,projectedLaw,totalLaw]
  change (if mode.1 = 0 then (0 : ℂ) else 1) • original.2 = _
  rw [originalLaw]
  by_cases zero : mode.1 = 0 <;> simp [zero]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)

/-- All-grade smooth representatives of the SAME full actual seven packet. -/
def sharedActualSevenCurves : SmoothLowPhysicalRow parameters lower positive
    (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) :=
  SmoothLowPhysicalRow.of_shifted parameters lower positive _
    (generalConjugatedFullSevenCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive data _ curves)
    (generalConjugatedFullSevenCurve_smooth parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive data _ curves
      (generalShared_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades))
    (generalConjugatedFullSevenCurve_actual parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive data _ curves allGrades)

/-- Literal original first radial RHS P(j+f), with genuine full-source rows. -/
def sharedActualXiRadialRHS : SmoothLowPhysicalRow parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) +
      strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 3) :=
  (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state
    (sharedActualSevenCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades) 0).add
      (ActualSourceRadialCurves.forceRow parameters lower positive lowerHalf data curves)

/-- The accepted actual coefficient PDE has the SAME P(j+f) coefficients. -/
theorem sharedActualXiRadialRHS_actual (mode : ℤ × ℤ) :
    (fun radius => (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
      curves allGrades mode radius).2) =ᵐ[volume.restrict (Icc lower 1)]
    fun radius => (sharedActualXiRadialRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades).meanFree.physicalCurve 0 radius mode := by
  let rhs := sharedActualXiRadialRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades
  let j := lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0
    (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))
  let f := strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 3
  filter_upwards [generalPhysicalRHSCurve_actual parameters length compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades mode,
    generalOriginalFullRHS_literal parameters length compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data),
    rhs.meanFree.physicalCurve_actual (lowerHalf.trans_lt (by norm_num)) 0,
    lowRhoPhysicalCoefficient_projection parameters lower positive (j+f),
    lowRhoPhysicalCoefficient_add_ae parameters lower positive j f] with radius actual literal same projected added
  exact xiPhysicalRHS_combine mode
    (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades mode radius)
    (generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive j radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive f radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive (j+f) radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive (Grad.SourceCollarFullSource.meanFreeRow lower (j+f)) radius mode)
    (rhs.meanFree.physicalCurve 0 radius mode)
    actual (congrArg Prod.snd (literal mode)) (added mode) (projected mode) (same mode)

end Grad.ActualPolarEquations
