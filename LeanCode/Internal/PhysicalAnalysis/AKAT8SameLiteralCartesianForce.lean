import AKAT7LiteralCartesianForceAlgebra
import AKAO13LiteralSameJAndC

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

/-- Both planar normalized rows are the literal Cartesian force expression
of the SAME reconstructed U. The only remaining radial term is radial−j;
no radial mean has been discarded in this identity. -/
theorem sharedFull_cartesianForce_polar (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (polar axial : ℝ) (radial : ComplexEuclidean 1) :
    let a := curves.covariant parameters length compact lower positive bounded state.val
    let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state.val
    let matrix := (rotatedPhysicalFrameMatrix parameters 1 1 state.val.val.epsilon state.val.val.field axial
      (polarClosedPoint radius polar (positive.le.trans inside.1) inside.2) * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
    let physical := (a.physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      state.val.val.low lower positive bounded).fullField bounded (radius,polar,axial)
    cartesianForceValue (cartesianCovariantValue polar (WithLp.toLp 2 ![radial 0,
      (curves.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial) 0,0]))
      (cartesianCovariantValue polar (rotated.fullField bounded (radius,polar,axial) + polarQuarter (a.fullField bounded (radius,polar,axial))))
      (cartesianCovariantValue polar (a.fullField bounded (radius,polar,axial))) ((2 : ℂ) • WithLp.toLp 2 (matrix.mulVec physical)) =
      cartesianCovariantValue polar (WithLp.toLp 2 ![
        radial 0-(curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).fullField bounded (radius,polar,axial) 0,
        (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,polar,axial) 0,0]) := by
  dsimp only
  rw [cartesianForceValue_matrix_polar]
  have radialContraction := originalRetainedForce_sameU parameters length compact lower positive bounded state.val
    (curves.covariant parameters length compact lower positive bounded state.val) radius inside (polar,axial)
  have j := fullField_originalJ parameters length compact lower positive bounded state curves radius inside (polar,axial)
  rw [radialContraction] at j
  have first := sharedFull_firstForce_pointwise parameters length compact lower positive bounded lengthPositive state.val data solution curves
    radius inside (polar,axial)
  have firstScalar := congrArg (fun value : ComplexEuclidean 1 => value 0) first
  dsimp only at firstScalar
  rw [PiLp.sub_apply,PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,
    fullField_forceCartesianU parameters length compact lower positive bounded state.val 0
      (curves.covariant parameters length compact lower positive bounded state.val) radius inside (polar,axial),
    (curves.rotatedCovariant parameters length compact lower positive bounded state.val).fullField_bulkUnit bounded (0 : Fin 1) 1 radius inside (polar,axial),
    (curves.covariant parameters length compact lower positive bounded state.val).fullField_bulkUnit bounded (0 : Fin 1) 0 radius inside (polar,axial)] at firstScalar
  simp only [ite_true,smul_eq_mul,matrixUnit_apply,operatorBasis,PiLp.smul_apply] at firstScalar
  dsimp at firstScalar
  congr 1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · dsimp
    linear_combination j
  · dsimp
    linear_combination firstScalar
  · rfl

end Grad.ActualCartesianEquations
