import AKDW16ActualOriginalKnownSourceCores
import AKDW11SameNativePreAxialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceFirst Grad.NonlinearQuotientBounds
namespace StartupSpatialAction

def knownGradientEntry (rank : ℕ) (direction : Fin 2) : StartupSpatialAction rank 2 3 1 1 :=
  (value rank (startupComponentEntry (2 : Fin 3) direction)).comp (covariantPrimitive rank)

theorem knownGradientEntry_controlled (parameters : PhaseParameters) (rank : ℕ) (direction : Fin 2) :
    (knownGradientEntry rank direction).OriginalEndpointControlled parameters :=
  (value_originalEndpointControlled parameters rank _).comp (covariantPrimitive_originalEndpointControlled parameters rank)

end StartupSpatialAction

def startupKnownGradientEntryCore (parameters : PhaseParameters) (force : ACore parameters 2) (direction : Fin 2) : ACore parameters 3 :=
  (StartupSpatialAction.fixedCore_exists parameters (StartupSpatialAction.knownGradientEntry 0 direction)
    (StartupSpatialAction.knownGradientEntry_controlled parameters 0 direction) force).choose

theorem startupKnownGradientEntryCore_same (parameters : PhaseParameters) (force : ACore parameters 2) (direction : Fin 2) :
    originalSourceFieldLinear parameters (startupKnownGradientEntryCore parameters force direction)=
      originalValueKernel (startupComponentEntry (2 : Fin 3) direction)
        (startupCovariantPrimitiveKernel (originalSourceFieldLinear parameters force)) :=
  (StartupSpatialAction.fixedCore_exists parameters (StartupSpatialAction.knownGradientEntry 0 direction)
    (StartupSpatialAction.knownGradientEntry_controlled parameters 0 direction) force).choose_spec

def startupKnownDeterminantFluxCore (parameters : PhaseParameters) (determinant : ACore parameters 1) (direction : Fin 2) : ACore parameters 3 :=
  (StartupSpatialAction.fixedCore_exists parameters (StartupSpatialAction.lowerScalarFlux 0 direction)
    (StartupSpatialAction.lowerScalarFlux_originalEndpointControlled parameters 0 direction) determinant).choose

theorem startupKnownDeterminantFluxCore_same (parameters : PhaseParameters) (determinant : ACore parameters 1) (direction : Fin 2) :
    originalSourceFieldLinear parameters (startupKnownDeterminantFluxCore parameters determinant direction)=
      startupLowerScalarFluxKernel direction (originalSourceFieldLinear parameters determinant) := by
  have same := (StartupSpatialAction.fixedCore_exists parameters (StartupSpatialAction.lowerScalarFlux 0 direction)
    (StartupSpatialAction.lowerScalarFlux_originalEndpointControlled parameters 0 direction) determinant).choose_spec
  simpa only [startupKnownDeterminantFluxCore,startupLowerScalarFluxKernel_coarse] using same

def startupKnownNativeFluxCore (parameters : PhaseParameters) (scale : ℝ)
    (determinant : ACore parameters 1) (force : ACore parameters 2) (direction : Fin 2) : ACore parameters 3 :=
  -startupKnownDeterminantFluxCore parameters determinant direction-
    (scale : ℂ) • originalSignedAxialCore parameters (startupKnownGradientEntryCore parameters force direction) 1 1 1

theorem startupSignedUnitCore_one {dimension : ℕ} (parameters : PhaseParameters) (core : ACore parameters dimension) :
    originalSignedAxialCore parameters core 1 1 1=timeDerivativeCore parameters core := by
  change ((1/1 : ℝ) : ℂ) • timeDerivativeCore parameters core=_
  simp only [div_self one_ne_zero,Complex.ofReal_one,one_smul]

/-- The genuine known part of the native flux costs one source cell
order, with no coefficient or unknown norm entering its payment. -/
theorem startupKnownNativeFluxCore_bound (parameters : PhaseParameters) (scale : ℝ) (grade : ℕ) (direction : Fin 2) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (determinant : ACore parameters 1) (force : ACore parameters 2),
      originalGradeNorm grade (startupKnownNativeFluxCore parameters scale determinant force direction)≤
        constant*(originalGradeNorm grade determinant+originalGradeNorm (grade+1) force) := by
  let firstCertificate := StartupSpatialAction.fixedCore_bound parameters
    (StartupSpatialAction.lowerScalarFlux grade direction)
    (StartupSpatialAction.lowerScalarFlux_originalEndpointControlled parameters grade direction)
  let first := firstCertificate.choose
  have firstNonnegative := firstCertificate.choose_spec.1
  have firstBound := firstCertificate.choose_spec.2
  let secondCertificate := StartupSpatialAction.fixedCore_bound parameters
    (StartupSpatialAction.knownGradientEntry (grade+1) direction)
    (StartupSpatialAction.knownGradientEntry_controlled parameters (grade+1) direction)
  let second := secondCertificate.choose
  have secondNonnegative := secondCertificate.choose_spec.1
  have secondBound := secondCertificate.choose_spec.2
  refine ⟨first+‖(scale : ℂ)‖*second,add_nonneg firstNonnegative (mul_nonneg (norm_nonneg _) secondNonnegative),?_⟩
  intro determinant force
  have determinantBound : originalGradeNorm grade (startupKnownDeterminantFluxCore parameters determinant direction)≤first*originalGradeNorm grade determinant := firstBound determinant (startupKnownDeterminantFluxCore parameters determinant direction)
    (by simpa only [startupLowerScalarFluxKernel_coarse] using startupKnownDeterminantFluxCore_same parameters determinant direction)
  have forceBound : originalGradeNorm (grade+1) (startupKnownGradientEntryCore parameters force direction)≤second*originalGradeNorm (grade+1) force := secondBound force (startupKnownGradientEntryCore parameters force direction)
    (startupKnownGradientEntryCore_same parameters force direction)
  have axialBound := (timeDerivativeCore_bound parameters grade (startupKnownGradientEntryCore parameters force direction)).trans forceBound
  have sumBound := originalGradeNorm_sub_le grade (-startupKnownDeterminantFluxCore parameters determinant direction)
    ((scale : ℂ) • originalSignedAxialCore parameters (startupKnownGradientEntryCore parameters force direction) 1 1 1)
  rw [originalGradeNorm_neg,originalGradeNorm_smul,startupSignedUnitCore_one] at sumBound
  have scaledAxial : ‖(scale : ℂ)‖*originalGradeNorm grade
      (timeDerivativeCore parameters (startupKnownGradientEntryCore parameters force direction))≤
      ‖(scale : ℂ)‖*(second*originalGradeNorm (grade+1) force) :=
    mul_le_mul_of_nonneg_left axialBound (norm_nonneg (scale : ℂ))
  rw [startupKnownNativeFluxCore,startupSignedUnitCore_one]
  nlinarith only [sumBound,determinantBound,scaledAxial,
    mul_nonneg firstNonnegative (originalGradeNorm_nonnegative (grade+1) force),
    mul_nonneg (mul_nonneg (norm_nonneg (scale : ℂ)) secondNonnegative) (originalGradeNorm_nonnegative grade determinant)]

end Grad.CartesianStartup
