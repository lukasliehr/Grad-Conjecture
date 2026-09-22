import AKAC1SmoothActualLowPhysicalRows
import AJG8SameFullCompletedCovariants

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularRestriction Grad.AnnularPhysicalReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularHighGenerators
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion Grad.AnnularCoupledInverse
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation

/-- Exact all-grade curves for the full original seven packet of the SAME
observed Cartesian-source solution. Incoming data are retained. -/
def actualCartesianSevenCurves
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
    SmoothLowPhysicalRow parameters lower positive
      (originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
        (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
          lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point.ofLp.1) := by
  let actual := actualCartesianObserved_fullSeven_smooth parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades
  exact SmoothLowPhysicalRow.of_shifted parameters lower positive _ actual.choose actual.choose_spec.1 actual.choose_spec.2

def SmoothLowPhysicalRow.covariant (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : AnnularReconstructionState parameters length compact)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (fullCovariantAction parameters length compact lower positive bounded.le state row) :=
  curves.action parameters lower positive bounded _
    (radialNormalizedCovariantKernel_regular parameters length compact state)
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state lower positive bounded)

def SmoothLowPhysicalRow.rotatedCovariant (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : AnnularReconstructionState parameters length compact)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (fullRotatedCovariantAction parameters length compact lower positive bounded.le state row) :=
  curves.action parameters lower positive bounded _
    (radialNormalizedRotatedCovariantKernel_regular parameters length compact state)
    (radialNormalizedRotatedCovariantKernel_conjugated_smooth parameters length compact state lower positive bounded)

end Grad.ActualSmoothPhysicalField
