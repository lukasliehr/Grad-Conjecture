import AKBC43SameTupleCurveTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1) (radius : Icc lower (1 : ℝ))

/-- All seven original slots are the SAME pressure/xi traces, with only
Rxi and xi divided by r. The copied homogeneous sources are literally zero. -/
theorem originalKernelTuple_normalizedInput :
    let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi total vector scalar)
    let pressure := (originalRawFluxCurves parameters length rho epsilon base small lower positive bounded
      (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
    tupleNormalizedInput parameters lower positive
      (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar) radius=
      WithLp.toLp 2 ![originalCurveNegativeRotation pressure radius,
        (radius.val : ℂ)⁻¹ • originalCurveNegativeRotation xi radius,originalCurveNegativeAxial xi radius,
        (radius.val : ℂ)⁻¹ • originalCurveNegativeTrace xi radius,0,0,0] := by
  dsimp only
  apply PiLp.ext
  intro slot
  fin_cases slot
  · exact tupleDifferentiatedTrace_sameRotation _ bounded _ 0 rfl radius
  · exact congrArg ((radius.val : ℂ)⁻¹ • ·) (tupleDifferentiatedTrace_sameRotation _ bounded _ 1 rfl radius)
  · exact tupleDifferentiatedTrace_sameAxial _ bounded _ 1 rfl radius
  · exact congrArg ((radius.val : ℂ)⁻¹ • ·) (tupleNegativeTrace_sameCurves _ bounded _ 1 rfl radius)
  · exact tupleNegativeTrace_zero _ 2 rfl radius
  · exact tupleDifferentiatedTrace_zero _ 2 rfl false radius
  · exact tupleNegativeTrace_zero _ 3 rfl radius

end Grad.OriginalKernelCovariantRecovery
