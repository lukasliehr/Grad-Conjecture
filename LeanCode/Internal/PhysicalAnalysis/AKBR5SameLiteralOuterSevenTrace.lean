import AKBR4SameFullOuterSevenCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularSmoothCore Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.AnnularLowEnergy
open Grad.AnnularUniformBoundary
open Grad.AnnularTiltedReference Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularOriginalSmoothCore Grad.AnnularFullGraph Grad.OriginalKernelGraphRestriction
variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower)
    (lowerHalf : lower≤1/2) (lengthPositive : 0<length) (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (point : OriginalFiveBlockAmbient parameters lower length positive)
    (represented : OriginalTupleObservation parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state tuple point)

include represented

/-- Original pressure observation gives x=Rp for an arbitrary represented
full graph point, including the excluded angular zero coefficient. -/
theorem originalObservedPressure_rotation (radius : Icc lower (1:ℝ)) (mode : ℤ×ℤ) :
    frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 0) radius.val mode=
      sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point.ofLp.1) 0 radius mode := by
  have algebra (index : ℤ×ℤ) (value : ComplexEuclidean 1)
      (mean : index.1=0 → value=0) :
      frequencyNumerator (some false) index • (angularInverseMultiplier index • value)=value := by
    by_cases zero : index.1=0
    · rw [mean zero]
      simp
    · rw [angularInverseMultiplier,if_neg zero,smul_smul]
      change (Complex.I*(index.1:ℂ)*(Complex.I*(index.1:ℂ))⁻¹) • _=_
      rw [mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero)),one_smul]
  apply (congrArg (fun value : ComplexEuclidean 1 => frequencyNumerator (some false) mode • value)
    (represented.pressure radius mode)).trans
  apply algebra
  intro zero
  rcases mode with ⟨angular,cell⟩
  change angular=0 at zero
  subst angular
  exact sameCoupledXCoefficient_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive _ 0 radius cell

/-- Exact equality of the full original outer seven tuple and the same
literal tuple's normalized trace at r=1. Both actual copied slots are zero. -/
theorem originalObserved_fullOuterSeven
    (firstZero : tuple.val 2=0) (secondZero : tuple.val 3=0) :
    originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point.ofLp.1) 0=
      tupleNormalizedInput parameters lower positive tuple ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩ := by
  let radius : Icc lower (1:ℝ) := ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩
  let candidate := originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point.ofLp.1
  have kernel : radialKernelParameters parameters (tupleRadius lower positive radius)=parameters := radialKernelParameters_one parameters
  apply PiLp.ext
  intro slot
  apply NegativeTrace.ext_coefficient parameters 0 0
  intro mode
  rw [originalFullOuterSeven_coefficient,originalOuterX_physical,originalOuterXi_physical]
  apply PiLp.ext
  intro component
  fin_cases component
  have actual := congrArg (fun value : ComplexEuclidean 7 => value slot)
    (tupleNormalizedInput_coefficient parameters lower positive tuple radius mode)
  rw [sevenSlotFlatten_coefficient,kernel] at actual
  change negativeTraceCoefficient parameters 0 0 (tupleNormalizedInput parameters lower positive tuple radius slot) mode 0=
    originalTupleNormalizedCoefficient parameters lower tuple radius mode slot at actual
  apply Eq.trans ?_ actual.symm
  have pressure := originalObservedPressure_rotation parameters length compact lower positive lowerHalf lengthPositive state tuple point represented radius mode
  have scalar := represented.scalar radius mode
  fin_cases slot
  · exact (congrArg (fun value : ComplexEuclidean 1 => value 0) pressure).symm
  · change _=((1:ℂ)⁻¹ • (frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 1) (1:ℝ) mode)) 0
    simp only [inv_one,one_smul]
    exact (congrArg (fun value : ComplexEuclidean 1 => ((Complex.I*(mode.1:ℂ)) • value) 0) scalar).symm
  · exact (congrArg (fun value : ComplexEuclidean 1 => ((Complex.I*(mode.2:ℂ)) • value) 0) scalar).symm
  · change _=((1:ℂ)⁻¹ • originalPhysicalCoefficient (tuple.val 1) (1:ℝ) mode) 0
    simp only [inv_one,one_smul]
    exact (congrArg (fun value : ComplexEuclidean 1 => value 0) scalar).symm
  · change 0=originalPhysicalCoefficient (tuple.val 2) (1:ℝ) mode 0
    simp [firstZero,originalPhysicalCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]
  · change 0=(frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 2) (1:ℝ) mode) 0
    simp [firstZero,originalPhysicalCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]
  · change 0=originalPhysicalCoefficient (tuple.val 3) (1:ℝ) mode 0
    simp [secondZero,originalPhysicalCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]

end Grad.OriginalKernelOuterUniqueness
