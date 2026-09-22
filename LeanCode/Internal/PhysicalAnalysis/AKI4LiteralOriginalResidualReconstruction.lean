import AKI3SameRadiusOriginalTupleTraces
import AHW28LiteralMeanFreePhysicalRV

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentLow

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ))

private abbrev point : RadialPoint := tupleRadius lower positive radius
private abbrev kernelParameters : PhaseParameters := radialKernelParameters parameters (point lower positive radius)

def tupleNormalizedInput : SevenSlotTrace (kernelParameters parameters lower positive radius) 0 0 :=
  radialNormalizedSevenInput parameters (point lower positive radius) 0 0
    (tupleSevenInput parameters lower positive tuple radius)

def tupleCovariantTrace : NegativeTrace (kernelParameters parameters lower positive radius) 0 0 3 :=
  fullNegativeKernelAction _ 0 0
    (radialCovariantKernel parameters length compact state.val.val (point lower positive radius)
      state.val.property (positive.trans_le radius.property.1))
    (sevenSlotFlatten _ 0 0 (tupleSevenInput parameters lower positive tuple radius))

def tupleRotatedCovariantTrace : NegativeTrace (kernelParameters parameters lower positive radius) 0 0 3 :=
  fullNegativeKernelAction _ 0 0
    (radialRotatedCovariantKernel parameters length compact state.val.val (point lower positive radius)
      state.val.property (positive.trans_le radius.property.1))
    (sevenSlotFlatten _ 0 0 (tupleSevenInput parameters lower positive tuple radius))

theorem tupleCovariantTrace_derivative :
    IsAngularDerivative (kernelParameters parameters lower positive radius) 0 0
      (tupleCovariantTrace parameters length compact lower positive state tuple radius)
      (tupleRotatedCovariantTrace parameters length compact lower positive state tuple radius) :=
  radialCovariantKernel_derivative parameters length compact state.val.val (point lower positive radius)
    state.val.property (positive.trans_le radius.property.1) 0 0 _
    (tupleSevenInput_supported parameters lower positive tuple radius)
    (tupleSevenInput_scalarDerivative parameters lower positive tuple radius)

/-- J is the literal first-force row R a1 - r1 ac, before P. -/
def tupleFirstRowTrace : NegativeTrace (kernelParameters parameters lower positive radius) 0 0 1 :=
  fullNegativeKernelAction _ 0 0 (coordinateProjectionKernel (kernelParameters parameters lower positive radius) 3 0)
    (tupleRotatedCovariantTrace parameters length compact lower positive state tuple radius) -
  fullNegativeKernelAction _ 0 0 (radialRetainedForceKernel parameters length compact state.val.val (point lower positive radius))
    (tupleCovariantTrace parameters length compact lower positive state tuple radius)

/-- The original b3 = rho_b ac + kappa3 xi/r, before its angular derivative. -/
def tupleBThreeTrace : NegativeTrace (kernelParameters parameters lower positive radius) 0 0 1 :=
  fullNegativeKernelAction _ 0 0 (radialSignedCofactorRowKernel parameters length compact state 2 (point lower positive radius))
    (tupleCovariantTrace parameters length compact lower positive state tuple radius) +
  (radius.val : ℂ)⁻¹ • fullNegativeKernelAction _ 0 0
    (radialSignedCofactorComponentKernel parameters length compact state 1 2 (point lower positive radius))
    (tupleNegativeTrace parameters lower positive tuple 1 radius)

/-- AH23's complete Vb, with its actual finite angular moment and outer P. -/
def tupleVTrace : NegativeTrace (kernelParameters parameters lower positive radius) 0 0 1 :=
  originalPhysicalVTrace parameters length compact state (point lower positive radius) 0 0
    (tupleCovariantTrace parameters length compact lower positive state tuple radius)
    (tupleNegativeTrace parameters lower positive tuple 1 radius)
    (tupleDifferentiatedTrace parameters lower positive tuple 1 false radius)

def tuplePhysicalRowTrace (row : Fin 3) : NegativeTrace (kernelParameters parameters lower positive radius) 0 0 1 :=
  fullNegativeKernelAction _ 0 0 (lowPhysicalRowKernel parameters length compact state row (point lower positive radius))
    (sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive tuple radius))

theorem tuplePhysicalRowTrace_first :
    tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 0 =
      tupleFirstRowTrace parameters length compact lower positive state tuple radius := by
  simp only [tuplePhysicalRowTrace, lowPhysicalRowKernel, ite_true,
    radialNormalizedUnprojectedFirstRowKernel, fullNegativeKernelAction_sub,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, tupleFirstRowTrace,
    tupleRotatedCovariantTrace, tupleCovariantTrace, radialRotatedCovariantKernel,
    radialCovariantKernel, radialSevenSlotKernel_action, tupleNormalizedInput]

theorem tupleBThreeTrace_normalized :
    tupleBThreeTrace parameters length compact lower positive state tuple radius =
      fullNegativeKernelAction _ 0 0 (radialNormalizedBThreeKernel parameters length compact state (point lower positive radius))
        (sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive tuple radius)) := by
  simp only [tupleBThreeTrace, radialNormalizedBThreeKernel, fullNegativeKernelAction_add,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, tupleCovariantTrace,
    radialCovariantKernel, radialSevenSlotKernel_action, sevenInputSlotKernel_flatten,
    tupleNormalizedInput]
  simp only [radialNormalizedSevenInput, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    tupleSevenInput, map_smul]
  rfl

theorem tuplePhysicalRowTrace_c_derivative :
    IsAngularDerivative (kernelParameters parameters lower positive radius) 0 0
      (tupleBThreeTrace parameters length compact lower positive state tuple radius)
      (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 1) := by
  rw [tupleBThreeTrace_normalized]
  change IsAngularDerivative _ 0 0 _ (fullNegativeKernelAction _ 0 0
    (radialNormalizedUnprojectedCKernel parameters length compact state (point lower positive radius))
    (sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive tuple radius)))
  apply radialNormalizedBThreeKernel_derivative
  · exact tupleSevenInput_supported parameters lower positive tuple radius
  · exact radialNormalizedSevenInput_derivative parameters (point lower positive radius) 0 0
      (tupleSevenInput parameters lower positive tuple radius)
      (tupleSevenInput_scalarDerivative parameters lower positive tuple radius)

theorem tuplePhysicalRowTrace_rV :
    tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 2 =
      (radius.val : ℂ) • tupleVTrace parameters length compact lower positive state tuple radius :=
  radialNormalizedPhysicalRVKernel_originalPhysical parameters length compact state (point lower positive radius)
    (positive.trans_le radius.property.1) 0 0 (tupleSevenInput parameters lower positive tuple radius)

/-- Literal AH24 residuals of the four fields. Neither residual is an
independent variable or an equation premise. -/
def originalTupleF1 (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  derivWithin (fun location => originalPhysicalCoefficient (tuple.val 1) location mode) (Icc lower 1) radius.val -
    angularMeanFreeMultiplier mode • negativeTraceCoefficient (kernelParameters parameters lower positive radius) 0 0
      (tupleFirstRowTrace parameters length compact lower positive state tuple radius) mode

def originalTupleG3 (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  derivWithin (fun location => originalPhysicalCoefficient (tuple.val 0) location mode) (Icc lower 1) radius.val +
    (radius.val : ℂ)⁻¹ • originalPhysicalCoefficient (tuple.val 0) radius.val mode +
    (length : ℂ)⁻¹ • ((Complex.I * (mode.2 : ℂ)) •
      (angularMeanFreeMultiplier mode • negativeTraceCoefficient (kernelParameters parameters lower positive radius) 0 0
        (tupleBThreeTrace parameters length compact lower positive state tuple radius) mode)) +
    negativeTraceCoefficient (kernelParameters parameters lower positive radius) 0 0
      (tupleVTrace parameters length compact lower positive state tuple radius) mode

end Grad.AnnularOriginalSmoothCore
