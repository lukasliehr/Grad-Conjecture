import AKBC31SameFrameCircleCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay Grad.OriginalKernelGraphRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollar Grad.ActualPhysicalField Grad.ActualForceMatrixFidelity Grad.ActualPolarEquations
open Grad.NonlinearRange

def originalForceCircle (parameters : PhaseParameters) (kind : Fin 2) (circle : CellL2 3) : CellL2 1 :=
  if kind=0 then (2 : ℂ) • originalCircleTangentialRow parameters circle
  else (-2 : ℂ) • originalCircleMatrix parameters (matrixUnit (0 : Fin 1) (2 : Fin 3)) circle

def originalForcePolarValue (kind : Fin 2) (angle : ℝ) (value : ComplexEuclidean 3) : ComplexEuclidean 1 :=
  if kind=0 then (2 : ℂ) • originalPolarTangentialValue value angle
  else (-2 : ℂ) • matrixUnit (0 : Fin 1) (2 : Fin 3) value

theorem originalForcePolarValue_pairing (kind : Fin 2) (angle : ℝ)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) (vector : ComplexEuclidean 3) :
    matrixPairing (if kind=0 then (2 : ℂ) • physicalTangentialVector angle else (-2 : ℂ) • physicalToroidalVector)
      matrix vector=originalForcePolarValue kind angle (WithLp.toLp 2 (matrix.mulVec vector)) 0 := by
  fin_cases kind <;> simp [originalForcePolarValue,matrixPairing,originalPolarTangentialValue,
    physicalTangentialVector,physicalToroidalVector,Matrix.mulVec,dotProduct,Fin.sum_univ_three,matrixUnit_apply,operatorBasis]
  all_goals ring

theorem originalForceCircle_represents {parameters : PhaseParameters} {radius : RadialPoint}
    {circle : CellL2 3} {source : ℝ×ℝ→ComplexEuclidean 3}
    (represented : OriginalCircleRepresents parameters radius circle source) (continuousSource : Continuous source) (kind : Fin 2) :
    OriginalCircleRepresents parameters radius (originalForceCircle parameters kind circle)
      (fun angles => originalForcePolarValue kind angles.1 (source angles)) := by
  fin_cases kind
  · exact (represented.tangential continuousSource).smul 2
  · exact (represented.valueMap continuousSource (matrixUnit (0 : Fin 1) (2 : Fin 3))).smul (-2)

variable (parameters : PhaseParameters) (length compact : ℝ) (nonzero : length≠0)
    (state : AnnularReconstructionState parameters length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (radius : Icc lower (1 : ℝ))

include nonzero

theorem originalForceProduct_sameCore (kind : Fin 2) (angles : ℝ×ℝ) :
    forceMatrixProduct parameters length state.val.data.epsilon state.val.data.field kind radius.val
      (positive.le.trans radius.property.1) radius.property.2
      (fun angles => (originalPolarCovariantCurves parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
        lower positive bounded vector).fullField bounded (radius.val,angles)) angles=
      originalForcePolarValue kind angles.1
        (originalCoreCircle parameters
          (originalCovariantCore parameters length state.val.data.epsilon state.val.data.field vector true)
          (tupleRadius lower positive radius) angles) := by
  let curves := originalPolarCovariantCurves parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
    lower positive bounded vector
  apply PiLp.ext
  intro component
  have only : component=0 := Subsingleton.elim _ _
  subst component
  calc
    _ = (physicalForceCurves parameters length compact lower positive bounded state kind curves).fullField
        bounded (radius.val,angles) 0 :=
      congrArg (fun value : ComplexEuclidean 1 => value 0)
        (fullField_forceMatrixProduct parameters length compact lower positive bounded state kind curves radius.val radius.property angles).symm
    _ = _ := by
      rw [fullField_forceCartesianU parameters length compact lower positive bounded state kind curves radius.val radius.property angles]
      have same := originalPolarCovariantCurves_recovers_U parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
        lower positive bounded vector radius.val radius.property angles
      change (curves.physicalUFromPolar parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
        lower positive bounded).fullField bounded (radius.val,angles)=_ at same
      rw [same,originalForcePolarValue_pairing]
      exact congrArg (fun value => originalForcePolarValue kind angles.1 value 0)
        (originalRotatedCovariantCore_value parameters length state.val.data.epsilon nonzero state.val.data.field vector _ _).symm

theorem originalForceNegative_circle (kind : Fin 2) :
    OriginalNegativeCircle parameters (tupleRadius lower positive radius)
      (fullNegativeKernelAction _ 0 0
        (radialForceKernel parameters length compact state.val (tupleRadius lower positive radius) kind 0)
        (originalCurveNegativeTrace
          (originalPolarCovariantCurves parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
            lower positive bounded vector) radius))
      (originalForceCircle parameters kind
        (originalCoreCircleTrace parameters
          (originalCovariantCore parameters length state.val.data.epsilon state.val.data.field vector true)
          (tupleRadius lower positive radius))) := by
  intro mode
  rw [originalForceNegative_product parameters length compact state.val lower positive _ bounded radius]
  have represented := originalForceCircle_represents
    (originalCoreCircleTrace_represents parameters
      (originalCovariantCore parameters length state.val.data.epsilon state.val.data.field vector true)
      (tupleRadius lower positive radius))
    (originalCoreCircle_continuous parameters _ (tupleRadius lower positive radius)) kind
  refine Eq.trans ?_ (represented mode).symm
  congr 1
  funext angles
  exact originalForceProduct_sameCore parameters length compact nonzero state lower positive bounded vector radius kind angles

end Grad.OriginalKernelCovariantRecovery
