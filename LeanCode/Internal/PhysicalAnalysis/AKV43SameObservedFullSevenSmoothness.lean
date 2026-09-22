import AKV35ActualObservedGraphRadialRegularity
import AKV42ActualCartesianFullSevenSmoothness

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
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion
open Grad.AnnularKnownLow
open Grad.AnnularRestriction Grad.AnnularCurrentLow Grad.AnnularForwardDatum
theorem originalSevenPacket_same_sources (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (first second : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (same : first.val.ofLp.1 = second.val.ofLp.1) :
    originalSevenPacket parameters lower length positive bounded lengthPositive first candidate =
      originalSevenPacket parameters lower length positive bounded lengthPositive second candidate := by
  exact (originalSevenPacket_decomposition parameters lower length positive bounded lengthPositive first candidate).trans
    ((congrArg (fun rows => homogeneousCoupledSevenInput parameters length lower lengthPositive positive
        (originalCoupledEquivalence parameters lower length positive bounded lengthPositive candidate) + knownLowSevenPacket lower rows)
      (congrArg (originalStoredKnownRows parameters lower positive bounded) same)).trans
        (originalSevenPacket_decomposition parameters lower length positive bounded lengthPositive second candidate).symm)

/-- The packet used for reconstruction from the actual Cartesian datum and
the observed retained field has the same smooth full seven curves, although
the actual solved incoming data may differ. -/
theorem actualCartesianObserved_fullSeven_smooth
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤
      originalCoefficientLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (point : OriginalFiveBlockAmbient parameters lower length positive)
    (member : point ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (sameSources : point.ofLp.2 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
        lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) weighted) :
    ∃ curve : ℕ → ℝ → CellL2 7,
      (∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)) ∧
      (∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
        curve grade radius mode = (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^(grade+1) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
                (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
                  lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point.ofLp.1) radius mode)) := by
  obtain ⟨⟨data,candidate⟩,equation,rfl⟩ := member
  have actual := actualCartesianEquation_fullSeven_smooth parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat data candidate equation sameSources allGrades
  have packet := originalSevenPacket_same_sources parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
    data (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) candidate sameSources
  rw [packet] at actual
  exact actual

end Grad.AnnularGeneralSourceRegularity
