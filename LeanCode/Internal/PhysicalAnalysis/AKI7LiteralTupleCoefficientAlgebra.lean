import AKI6SameResponseWeightedFourFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ))

/-- All normalized original coordinates, with the genuine full F0 slot. -/
def originalTupleNormalizedCoefficient (mode : ℤ × ℤ) : ComplexEuclidean 7 :=
  WithLp.toLp 2 ![
    (frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 0) radius.val mode) 0,
    ((radius.val : ℂ)⁻¹ • (frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 1) radius.val mode)) 0,
    (frequencyNumerator (some true) mode • originalPhysicalCoefficient (tuple.val 1) radius.val mode) 0,
    ((radius.val : ℂ)⁻¹ • originalPhysicalCoefficient (tuple.val 1) radius.val mode) 0,
    originalPhysicalCoefficient (tuple.val 2) radius.val mode 0,
    (frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 2) radius.val mode) 0,
    originalPhysicalCoefficient (tuple.val 3) radius.val mode 0]

theorem tupleNormalizedInput_coefficient (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive tuple radius)) mode =
      originalTupleNormalizedCoefficient parameters lower tuple radius mode := by
  ext slot
  rw [sevenSlotFlatten_coefficient]
  fin_cases slot <;>
    simp [tupleNormalizedInput, radialNormalizedSevenInput, tupleSevenInput,
      negativeTraceCoefficient_smul, tupleNegativeTrace_coefficient, tupleDifferentiatedTrace_coefficient,
      originalTupleNormalizedCoefficient] <;> exact Or.inl rfl

/-- The first residual is precisely xi_r - R(P a1) + P(r1 ac). -/
theorem originalTupleF1_AH24 (mode : ℤ × ℤ) :
    originalTupleF1 parameters length compact lower positive state tuple radius mode =
      derivWithin (fun location => originalPhysicalCoefficient (tuple.val 1) location mode) (Icc lower 1) radius.val -
        (Complex.I * (mode.1 : ℂ)) •
          (angularMeanFreeMultiplier mode • WithLp.toLp 2
            (fun _ : Fin 1 => negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
              (tupleCovariantTrace parameters length compact lower positive state tuple radius) mode 0)) +
        angularMeanFreeMultiplier mode • negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
          (fullNegativeKernelAction _ 0 0
            (radialRetainedForceKernel parameters length compact state.val.val (tupleRadius lower positive radius))
            (tupleCovariantTrace parameters length compact lower positive state tuple radius)) mode := by
  have derivative := tupleCovariantTrace_derivative parameters length compact lower positive state tuple radius mode
  have projected : angularMeanFreeMultiplier mode •
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (fullNegativeKernelAction _ 0 0 (coordinateProjectionKernel _ 3 0)
          (tupleRotatedCovariantTrace parameters length compact lower positive state tuple radius)) mode =
      (Complex.I * (mode.1 : ℂ)) • (angularMeanFreeMultiplier mode • WithLp.toLp 2
        (fun _ : Fin 1 => negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
          (tupleCovariantTrace parameters length compact lower positive state tuple radius) mode 0)) := by
    ext slot
    fin_cases slot
    change _ * negativeTraceCoefficient _ 0 0 (fullNegativeKernelAction _ 0 0 (coordinateProjectionKernel _ 3 0) _) mode 0 = _
    rw [coordinateProjectionKernel_action_coefficient, derivative]
    change angularMeanFreeMultiplier mode * ((Complex.I * (mode.1 : ℂ)) * _) =
      (Complex.I * (mode.1 : ℂ)) * (angularMeanFreeMultiplier mode * _)
    ring_nf
    rfl
  unfold originalTupleF1 tupleFirstRowTrace
  rw [negativeTraceCoefficient_sub, smul_sub]
  change _ - (angularMeanFreeMultiplier mode • negativeTraceCoefficient _ 0 0
    (fullNegativeKernelAction _ 0 0 (coordinateProjectionKernel _ 3 0) _) mode - _) = _
  rw [projected]
  abel

theorem tupleVTrace_meanFree (cell : ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleVTrace parameters length compact lower positive state tuple radius) (0, cell) = 0 := by
  unfold tupleVTrace originalPhysicalVTrace
  dsimp only
  simp only [angularMeanFreeKernel, scalarModeDiagonalKernel_action_coefficient]
  simp [angularMeanFreeMultiplier]

end Grad.AnnularOriginalSmoothCore
