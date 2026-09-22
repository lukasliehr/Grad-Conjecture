import AKAT10ExactRadialMeanProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualPolarFlux Grad.ActualForceMatrixFidelity Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.AnnularClosedJointRegularity

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.AnnularSourceGraph
/-- The literal Cartesian differential expression of the SAME original
reconstructed pair, with the full physical frame correction. -/
def sameCartesianRawForce (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) : ComplexEuclidean 3 :=
  let a := curves.covariant parameters length compact lower positive bounded state.val
  let matrix := (rotatedPhysicalFrameMatrix parameters 1 1 state.val.val.epsilon state.val.val.field axial
    (polarClosedPoint radius polar (positive.le.trans inside.1) inside.2) * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
  let physical := (a.physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded).fullField bounded (radius,polar,axial)
  cartesianForceValue
    (planarGradientValue (fderiv ℝ (cartesianPhysicalField
      (originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1)) (polarPlane (radius,polar),axial)))
    (fderiv ℝ (a.cartesianCovariant.cartesianField bounded) (polarPlane (radius,polar),axial)
      (radius • planeQuarterTurn (radialDirection polar),0))
    (a.cartesianCovariant.fullField bounded (radius,polar,axial)) ((2 : ℂ) • WithLp.toLp 2 (matrix.mulVec physical))

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
include allGrades smooth

theorem sameCartesianRawForce_from_radial (radius : ℝ) (inside : radius ∈ Ioo lower 1)
    (polar axial : ℝ) (radial : ComplexEuclidean 1)
    (radialLaw : HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,polar,axial))
      radial (Icc lower 1) radius) :
    sameCartesianRawForce parameters length compact lower positive bounded lengthPositive state data solution curves radius ⟨inside.1.le,inside.2.le⟩ polar axial =
      cartesianCovariantValue polar (WithLp.toLp 2 ![
        radial 0-(curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).fullField bounded (radius,polar,axial) 0,
        (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,polar,axial) 0,0]) :=
  sharedFull_cartesianForce_derivatives parameters length compact lower positive bounded lengthPositive state data solution curves allGrades smooth
    radius inside polar axial radial radialLaw

end Grad.ActualCartesianEquations
