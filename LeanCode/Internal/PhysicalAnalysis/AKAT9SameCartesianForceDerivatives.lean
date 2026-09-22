import AKAT8SameLiteralCartesianForce

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
variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
include allGrades smooth

/-- Literal AM18 differential expression for the SAME actual Cartesian
fields, before its one radial projection. Every partial derivative here is
the genuine Frechet derivative of the reconstructed physical field. -/
theorem sharedFull_cartesianForce_derivatives (radius : ℝ) (inside : radius ∈ Ioo lower 1)
    (polar axial : ℝ) (radial : ComplexEuclidean 1)
    (radialLaw : HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,polar,axial))
      radial (Icc lower 1) radius) :
    let a := curves.covariant parameters length compact lower positive bounded state.val
    let matrix := (rotatedPhysicalFrameMatrix parameters 1 1 state.val.val.epsilon state.val.val.field axial
      (polarClosedPoint radius polar (positive.le.trans inside.1.le) inside.2.le) * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
    let physical := (a.physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      state.val.val.low lower positive bounded).fullField bounded (radius,polar,axial)
    cartesianForceValue
      (planarGradientValue (fderiv ℝ (cartesianPhysicalField
        (originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1)) (polarPlane (radius,polar),axial)))
      (fderiv ℝ (a.cartesianCovariant.cartesianField bounded) (polarPlane (radius,polar),axial)
        (radius • planeQuarterTurn (radialDirection polar),0))
      (a.cartesianCovariant.fullField bounded (radius,polar,axial)) ((2 : ℂ) • WithLp.toLp 2 (matrix.mulVec physical)) =
      cartesianCovariantValue polar (WithLp.toLp 2 ![
        radial 0-(curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).fullField bounded (radius,polar,axial) 0,
        (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,polar,axial) 0,0]) := by
  dsimp only
  rw [fullSeven_physicalXi_cartesianGradient parameters lower length positive bounded lengthPositive data solution allGrades smooth curves radius inside polar axial radial radialLaw,
    sharedCartesianCovariant_cartesian_rotation parameters length compact lower positive bounded lengthPositive state.val data solution curves radius inside polar axial,
    (curves.covariant parameters length compact lower positive bounded state.val).fullField_cartesianCovariant bounded radius ⟨inside.1.le,inside.2.le⟩ (polar,axial)]
  exact sharedFull_cartesianForce_polar parameters length compact lower positive bounded lengthPositive state data solution curves
    radius ⟨inside.1.le,inside.2.le⟩ polar axial radial

end Grad.ActualCartesianEquations
