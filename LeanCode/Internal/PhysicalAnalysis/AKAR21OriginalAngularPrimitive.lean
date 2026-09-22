import AKAR20OriginalCoreCircleTrace
import GPA2ClosedPolarAngular
import ANH7HighOrbits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.BoundaryLift Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.Constraints Grad.ActualPhysicalAngular Grad.CircularHighWeak

variable {dimension : ℕ}

def OriginalCircleRotation (field rotated : CellL2 dimension) : Prop :=
  ∀ mode : ℤ × ℤ, rotated mode = (Complex.I*(mode.1 : ℂ)) • field mode

def originalCircleAngularInverse (parameters : PhaseParameters) (dimension : ℕ) : CellL2 dimension →L[ℂ] CellL2 dimension :=
  coefficientOperator parameters 0 (Equiv.refl _)
    (fun mode => angularInverseMultiplier mode • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) zero_le_one
    (fun mode => (ContinuousLinearMap.opNorm_smul_le _ _).trans
      ((mul_le_mul (angularInverseMultiplier_norm_le mode) ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)))

theorem originalCircleAngularInverse_norm (parameters : PhaseParameters) (dimension : ℕ) :
    ‖originalCircleAngularInverse parameters dimension‖ ≤ 1 := coefficientOperator_norm_le _ _ _ _ _ _

theorem originalCircleAngularInverse_apply (parameters : PhaseParameters) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    originalCircleAngularInverse parameters dimension field mode = angularInverseMultiplier mode • field mode := rfl

theorem originalCircleAngularInverse_rotation (parameters : PhaseParameters) (field rotated : CellL2 dimension)
    (rotation : OriginalCircleRotation field rotated) (mean : ∀ cell,field (0,cell)=0) :
    originalCircleAngularInverse parameters dimension rotated = field := by
  apply lp.ext
  funext mode
  rw [originalCircleAngularInverse_apply,rotation]
  by_cases zero : mode.1=0
  · rw [show mode=(0,mode.2) from Prod.ext zero rfl,mean]
    simp
  · rw [angularInverseMultiplier,if_neg zero,inv_smul_smul₀]
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast zero)

theorem originalCoreCircleTrace_unweighted (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : RadialPoint) (mode : ℤ × ℤ) :
    lambdaCircleCoefficient parameters radius.val (originalCoreCircleTrace parameters field radius) mode =
      angularCoefficient (fun angle => (field.val mode.2).value
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) mode.1 := by
  rw [originalCoreCircleTrace_represents parameters field radius mode]
  unfold doubleCoefficient
  simp_rw [originalCoreCircle_axialCoefficient]

theorem originalPolar_rotationCoefficient (field : ClosedJet dimension) (radius : RadialPoint) (mode : ℤ) :
    angularCoefficient (fun angle => (rotationJet field).value
      (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) mode =
      (Complex.I*(mode : ℂ)) • angularCoefficient (fun angle => field.value
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) mode := by
  have actual := angularCoefficient_angularJet 1 (originalPolarValue field) (originalPolarValue_smooth field)
    (originalPolarValue_periodic field) radius.val mode
  simp_rw [originalPolar_angularJet field radius.val _ radius.property.1 radius.property.2,
    originalPolarValue_closed field radius.val _ radius.property.1 radius.property.2] at actual
  simpa only [pow_one] using actual

theorem originalCoreCircleTrace_rotation (parameters : PhaseParameters) (field : ACore parameters dimension) (radius : RadialPoint) :
    OriginalCircleRotation (originalCoreCircleTrace parameters field radius)
      (originalCoreCircleTrace parameters (rotationCore parameters field) radius) := by
  intro mode
  rw [← lambdaCircle_weighted parameters radius.val (originalCoreCircleTrace parameters (rotationCore parameters field) radius) mode,
    ← lambdaCircle_weighted parameters radius.val (originalCoreCircleTrace parameters field radius) mode,
    originalCoreCircleTrace_unweighted,originalCoreCircleTrace_unweighted]
  change (_ : ℂ) • angularCoefficient (fun angle => (rotationJet (field.val mode.2)).value _) mode.1 = _
  rw [originalPolar_rotationCoefficient,smul_comm]

theorem originalCoreCircleTrace_mean (parameters : PhaseParameters) (field : ACore parameters dimension)
    (mean : angularCore parameters 0 field=0) (radius : RadialPoint) (cell : ℤ) :
    originalCoreCircleTrace parameters field radius (0,cell)=0 := by
  rw [← lambdaCircle_weighted parameters radius.val (originalCoreCircleTrace parameters field radius) (0,cell),
    originalCoreCircleTrace_unweighted]
  have projection := orbitCoefficient_projection (field.val cell)
    (Grad.SourceCollarDivision.polarClosedPoint radius.val 0 radius.property.1 radius.property.2) 0
  simp_rw [polarClosedPoint_orbit] at projection
  have zero : angularClosedJet 0 (field.val cell)=0 := congrArg (fun core : ACore parameters dimension => core.val cell) mean
  rw [zero] at projection
  rw [projection]
  simp

/-- The exact original mean-free scalar is recovered by K on its actual R
trace, before it is compared with any completed annular representative. -/
theorem originalKernelXi_circle_primitive (parameters : PhaseParameters) (base vector : ACore parameters 3)
    (scalar : ACore parameters 1) (radius : RadialPoint) :
    originalCoreCircleTrace parameters (originalKernelXi base vector scalar) radius =
      originalCircleAngularInverse parameters 1
        (originalCoreCircleTrace parameters (rotationCore parameters (originalKernelXi base vector scalar)) radius) := by
  symm
  exact originalCircleAngularInverse_rotation parameters _ _ (originalCoreCircleTrace_rotation parameters _ radius)
    (originalCoreCircleTrace_mean parameters _ (originalKernelXi_mean base vector scalar) radius)

end Grad.OriginalKernelRetainedDecay
