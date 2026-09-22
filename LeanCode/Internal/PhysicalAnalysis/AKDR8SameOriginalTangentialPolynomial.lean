import AKDR7OriginalRecoveredGradientNorm
import AKDB3SameScalarPolynomialGraph
import SBT3TangentialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualOriginalSourceMoments
open Grad.ActualScalarWeakEquations Grad.ActualSmoothPhysicalField Grad.Constraints
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision

theorem startupTangentialPolynomialKernel_ae (field : StartupL2 2) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (startupTangentialPolynomialKernel field) point cell =
        ((point 0 : ℝ) : ℂ) • startupComponentEntry 0 1 (field point cell) -
          ((point 1 : ℝ) : ℂ) • startupComponentEntry 0 0 (field point cell) := by
  let first := startupSmoothDiskMultiplier 1 (angularRotationCoordinate 0) (angularRotationCoordinate 0).contDiff
    (originalValueKernel (startupComponentEntry 0 0) field)
  let second := startupSmoothDiskMultiplier 1 (angularRotationCoordinate 1) (angularRotationCoordinate 1).contDiff
    (originalValueKernel (startupComponentEntry 0 1) field)
  filter_upwards [startupSmoothDiskMultiplier_same 1 _ (angularRotationCoordinate 0).contDiff
      (originalValueKernel (startupComponentEntry 0 0) field),
    startupSmoothDiskMultiplier_same 1 _ (angularRotationCoordinate 1).contDiff
      (originalValueKernel (startupComponentEntry 0 1) field),
    startupPointKernel_field_ae (startupComponentEntry (0 : Fin 1) (0 : Fin 2)) (LinearIsometryEquiv.refl ℝ _) field,
    startupPointKernel_field_ae (startupComponentEntry (0 : Fin 1) (1 : Fin 2)) (LinearIsometryEquiv.refl ℝ _) field,
    Lp.coeFn_add first second] with point one two firstValue secondValue added
  intro cell
  change ∀ cell, (originalValueKernel (startupComponentEntry (0 : Fin 1) (0 : Fin 2)) field) point cell =
    startupComponentEntry 0 0 (field point cell) at firstValue
  change ∀ cell, (originalValueKernel (startupComponentEntry (0 : Fin 1) (1 : Fin 2)) field) point cell =
    startupComponentEntry 0 1 (field point cell) at secondValue
  change (first+second) point cell = _
  rw [added]
  simp only [lp.coeFn_add,Pi.add_apply]
  rw [one cell,two cell,firstValue cell,secondValue cell]
  simp only [angularRotationCoordinate,ite_true,show (1 : Fin 2)≠0 by decide,ite_false,
    neg_apply,PiLp.proj_apply,Complex.ofReal_neg,neg_smul]
  abel

theorem originalTangentialPolynomial_sameField (parameters : PhaseParameters)
    (field : ACore parameters 2) :
    originalSourceFieldLinear parameters (tangentialBoundaryCore parameters field) =
      startupTangentialPolynomialKernel (originalSourceFieldLinear parameters field) := by
  apply startupField_ae_ext
  filter_upwards [originalSource_field_closed parameters (tangentialBoundaryCore parameters field),
    originalSource_field_closed parameters field,
    startupTangentialPolynomialKernel_ae (originalSourceFieldLinear parameters field),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point outputSame inputSame polynomial inside
  intro cell
  change (originalSourceMoments parameters (tangentialBoundaryCore parameters field)).field point cell = _
  rw [outputSame cell,polynomial cell]
  change _ = ((point 0 : ℝ) : ℂ) • startupComponentEntry 0 1 ((originalSourceMoments parameters field).field point cell) -
    ((point 1 : ℝ) : ℂ) • startupComponentEntry 0 0 ((originalSourceMoments parameters field).field point cell)
  rw [inputSame cell]
  simp only [closedDiskLift,dif_pos (openDiskMembershipClosed point inside),phaseWeightedJet_value]
  apply PiLp.ext
  intro coordinate
  have unique : coordinate=0 := Subsingleton.elim _ _
  subst coordinate
  simp only [PiLp.smul_apply,PiLp.sub_apply,tangentialBoundaryCore_value,startupComponentEntry,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,PiLp.single_apply,ite_true,mul_one,
    Complex.real_smul,smul_eq_mul]
  ring

end Grad.OriginalCoreRealization
