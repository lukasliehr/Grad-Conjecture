import AKBU12ActualOriginalRetainedUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularCoupledInverse Grad.AnnularOriginalCoreRealization
open Grad.AnnularOriginalSmoothCore Grad.AnnularFullGraph Grad.AnnularWeakExhaustion Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.OriginalKernelGraphRestriction

theorem originalXiCoefficient_zero (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower)
    (bounded : lower<1) (lengthPositive : 0<length) (radius : Icc lower (1:ℝ)) (mode : ℤ×ℤ) :
    sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive 0 0 radius mode=0 :=
  congrFun (congrFun (map_zero (coupledXiPhysicalLinear parameters lower length positive bounded lengthPositive)) radius) mode

theorem originalXCoefficient_zero (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower)
    (bounded : lower<1) (lengthPositive : 0<length) (radius : Icc lower (1:ℝ)) (mode : ℤ×ℤ) :
    sameCoupledXCoefficient parameters lower length positive bounded lengthPositive 0 0 radius mode=0 :=
  congrFun (congrFun (map_zero (coupledXPhysicalLinear parameters lower length positive bounded lengthPositive)) radius) mode

/-- Zero retained graph coordinates force the SAME tuple's original p and
Xi Fourier coefficients to vanish at every closed collar point. -/
theorem originalObservedTuple_retainedZero
    (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (lengthPositive : 0<length) (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (point : OriginalFiveBlockAmbient parameters lower length positive)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple point)
    (zero : originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive point=0)
    (radius : Icc lower (1:ℝ)) (mode : ℤ×ℤ) :
    originalPhysicalCoefficient (tuple.val 0) radius.val mode=0 ∧ originalPhysicalCoefficient (tuple.val 1) radius.val mode=0 := by
  have first := represented.pressure radius mode
  have second := represented.scalar radius mode
  change originalPhysicalCoefficient (tuple.val 0) radius.val mode=angularInverseMultiplier mode •
    sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
      (originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive point) 0 radius mode at first
  change originalPhysicalCoefficient (tuple.val 1) radius.val mode=
    sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive
      (originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive point) 0 radius mode at second
  rw [zero,originalXCoefficient_zero,smul_zero] at first
  rw [zero,originalXiCoefficient_zero] at second
  exact ⟨first,second⟩

/-- All original seven slots vanish once the four actual fields' Fourier
coefficients vanish. The differentiated slots are the existing exact Fourier derivatives. -/
theorem originalTuple_sevenZero
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower)
    (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1:ℝ))
    (zero : ∀ slot mode,originalPhysicalCoefficient (tuple.val slot) radius.val mode=0) :
    tupleSevenInput parameters lower positive tuple radius=0 := by
  have value (slot : Fin 4) : tupleNegativeTrace parameters lower positive tuple slot radius=0 := by
    apply NegativeTrace.ext_coefficient _ 0 0
    intro mode
    rw [tupleNegativeTrace_coefficient,zero]
    exact (negativeTraceCoefficientCLM _ 0 0 mode).map_zero.symm
  have derivative (slot : Fin 4) (axis : Bool) : tupleDifferentiatedTrace parameters lower positive tuple slot axis radius=0 := by
    apply NegativeTrace.ext_coefficient _ 0 0
    intro mode
    rw [tupleDifferentiatedTrace_coefficient,zero,smul_zero]
    exact (negativeTraceCoefficientCLM _ 0 0 mode).map_zero.symm
  apply PiLp.ext
  intro slot
  fin_cases slot
  · exact derivative 0 false
  · exact derivative 1 false
  · exact derivative 1 true
  · exact value 1
  · exact value 2
  · exact derivative 2 false
  · exact value 3

end Grad.OriginalPhysicalKernelUniqueness
