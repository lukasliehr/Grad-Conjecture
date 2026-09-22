import AKBD21OriginalPolarDeterminantConsumer
import AKBD27SameCartesianDeterminantConversion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.ActualOriginalThirdSource

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low lower positive bounded 0 source flat).val.ofLp.1)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution))
    (forces : ∀ component : Fin 3, SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) (primitiveKnownSlot component)))


variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive bounded.le 0 0
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data)).ofLp.1.ofLp.2)

open Grad.ActualCartesianDescent Grad.PhysicalFamily

include same allGrades smooth

/-- Actual original-data determinant equation on every punctured collar.
The only differential inputs are the genuine SAME Xi and corrected-p radial
laws, supplied by AKAK and AKBB. No source correction or mean is assumed. -/
theorem actualOriginalCartesianDeterminant_from_radial (radius : ℝ) (inside : radius ∈ Ioo lower 1)
    (xiRadial : ∀ angles, HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,angles))
      (((curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).add (forces 0)).meanFree.fullField bounded (radius,angles))
      (Icc lower 1) radius)
    (pRadial : ∀ angles,
      scalarDirectionalField (curves.correctedP parameters length compact lower positive bounded state) bounded 0 (1,0,0) (radius,angles) =
      removePolarMean (fun query =>
        -(curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,query) 0 / (radius : ℂ) -
        scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,query) / (length : ℂ) -
        (curves.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,query) 0 / (radius : ℂ) +
        third.fullField bounded (radius,query) 0) angles)
    (angles : ℝ × ℝ) :
    removePolarMean (fun query => cartesianDeterminantDivergence length
      ((samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.cartesianField bounded)
      (polarPlane (radius,query.1),query.2)) angles =
      corePolarValue parameters (source 2) radius (positive.le.trans inside.1.le) inside.2.le angles 0 := by
  have polar := actualOriginalPolarDeterminant_from_radial parameters length compact lower positive bounded state lengthPositive
    source flat data same solution curves forces allGrades smooth third radius inside xiRadial pRadial angles
  let divergence := polarDeterminantDivergence parameters length compact lower positive bounded state lengthPositive
    (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution curves radius
  have conversion : (fun query : ℝ × ℝ => cartesianDeterminantDivergence length
      ((samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.cartesianField bounded)
      (polarPlane (radius,query.1),query.2)) = fun query => (length : ℂ)*divergence query := by
    funext query
    exact sameCartesianCofactorFlux_divergence parameters length compact lower positive bounded state lengthPositive
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution curves radius inside query.1 query.2
  apply (congrArg (fun field : ℝ × ℝ → ℂ => removePolarMean field angles) conversion).trans
  have scaled := congrFun (removePolarMean_smul (length : ℂ) divergence) angles
  change removePolarMean (fun query => (length : ℂ)*divergence query) angles = (length : ℂ)*removePolarMean divergence angles at scaled
  apply scaled.trans
  rw [polar,mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt lengthPositive))]

end Grad.ActualDeterminantEquations
