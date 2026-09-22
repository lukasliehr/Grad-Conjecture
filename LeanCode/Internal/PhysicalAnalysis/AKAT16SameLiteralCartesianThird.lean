import AKAT15SameCartesianXiAxial

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

open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.AnnularSourceGraph Grad.SourceCollarFullSource

/-- Literal normalized AM19, with the original length multiplying Rb and
both force-frame derivative contributions retained. -/
def sameCartesianThirdExpression (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) : ℂ :=
  let a := curves.covariant parameters length compact lower positive bounded state.val
  (length : ℂ) * fderiv ℝ (a.cartesianCovariant.cartesianField bounded) (polarPlane (radius,polar),axial)
      (radius • planeQuarterTurn (radialDirection polar),0) 2 -
    fderiv ℝ (cartesianPhysicalField (originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1))
      (polarPlane (radius,polar),axial) (0,1) 0 +
    (length : ℂ) * removePolarMean (fun query =>
      matrixPairing ((-2 : ℂ) • physicalToroidalVector)
        (rotatedPhysicalFrameMatrix parameters 1 1 state.val.val.epsilon state.val.val.field query.2
          (polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
        ((a.physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
          state.val.val.low lower positive bounded).fullField bounded (radius,query))) (polar,axial)

private theorem thirdNormalization (length : ℂ) (nonzero : length ≠ 0) (rotated axial correction source : ℂ)
    (equation : rotated+correction-length⁻¹*axial=source) :
    length*rotated-axial+length*correction=length*source := by
  rw [← equation]
  field_simp [nonzero]
  ring

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
include allGrades smooth

theorem sameCartesianThirdExpression_eq (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    sameCartesianThirdExpression parameters length compact lower positive bounded lengthPositive state data solution curves
      radius ⟨inside.1.le,inside.2.le⟩ polar axial =
      (length : ℂ) * (curves.bulkUnit (0 : Fin 1) 6).fullField bounded (radius,polar,axial) 0 := by
  let a := curves.covariant parameters length compact lower positive bounded state.val
  let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state.val
  let force := physicalForceCurves parameters length compact lower positive bounded state.val 1 a
  have closedInside : radius ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have third := sharedFull_thirdForce_pointwise parameters length compact lower positive bounded lengthPositive state.val data solution curves
    radius closedInside (polar,axial)
  have scalar := congrArg (fun value : ComplexEuclidean 1 => value 0) third
  dsimp only at scalar
  rw [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,
    rotated.fullField_bulkUnit bounded (0 : Fin 1) 2 radius closedInside (polar,axial)] at scalar
  change _ + (removePolarMean (fun query => force.fullField bounded (radius,query)) (polar,axial)) 0 - _ = _ at scalar
  rw [removePolarMean_coordinate _ (force.fullField_continuous_angles bounded radius closedInside)] at scalar
  have forceSame := funext (fun query => fullField_forceCartesianU parameters length compact lower positive bounded state.val 1 a radius closedInside query)
  change (fun query => force.fullField bounded (radius,query) 0) = _ at forceSame
  rw [forceSame] at scalar
  simp only [smul_eq_mul,matrixUnit_apply,operatorBasis,PiLp.smul_apply] at scalar
  dsimp at scalar
  simp only [mul_one] at scalar
  dsimp only [sameCartesianThirdExpression]
  rw [sharedCartesianCovariant_cartesian_rotation parameters length compact lower positive bounded lengthPositive state.val data solution curves radius inside polar axial,
    fullSeven_physicalXi_cartesianAxial parameters lower length positive bounded lengthPositive data solution allGrades smooth curves radius inside polar axial,
    cartesianCovariantValue_apply]
  change (length : ℂ) * (rotated.fullField bounded (radius,polar,axial) 2 + 0) -
    (curves.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,polar,axial) 0 + _ = _
  rw [add_zero]
  exact thirdNormalization (length : ℂ) (Complex.ofReal_ne_zero.mpr lengthPositive.ne') _ _ _ _ scalar

end Grad.ActualCartesianEquations
