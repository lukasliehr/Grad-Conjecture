import AKV34ActualCartesianEquationRadialRegularity
import AKV20GeneralActualFullSevenCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.AnnularKnownLow
open Grad.AnnularRestriction Grad.AnnularCurrentLow
/-- The original full seven packet has smooth all-grade Hilbert curves with
exact same-radius, same-width coefficients. All independent sources enter once. -/
theorem actualCartesianEquation_fullSeven_smooth
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤
      originalCoefficientLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate)
    (sameSources : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
        lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) weighted) :
    ∃ curve : ℕ → ℝ → CellL2 7,
      (∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)) ∧
      (∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
        curve grade radius mode = (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^(grade+1) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive data candidate) radius mode)) := by
  let curves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources
  have smooth := actualCartesianEquation_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat data candidate equation sameSources allGrades
  let weightedField := originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate
  refine ⟨generalConjugatedFullSevenCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    _ weightedField curves,?_,?_⟩
  · exact generalConjugatedFullSevenCurve_smooth parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
      _ weightedField curves smooth
  · exact generalConjugatedFullSevenCurve_actual parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
      _ weightedField curves allGrades

end Grad.AnnularGeneralSourceRegularity
