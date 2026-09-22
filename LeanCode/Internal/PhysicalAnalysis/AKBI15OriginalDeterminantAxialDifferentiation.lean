import AKBI14OriginalDeterminantProductDifferentiation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery

theorem originalDeterminant_time {parameters : PhaseParameters} (first second third : ACore parameters 3) :
    timeDerivativeCore parameters (determinantOperation parameters first second third)=
      determinantOperation parameters (timeDerivativeCore parameters first) second third+
      determinantOperation parameters first (timeDerivativeCore parameters second) third+
      determinantOperation parameters first second (timeDerivativeCore parameters third) := by
  apply coreValue_ext
  intro point angle
  let fields : Fin 3 → ACore parameters 3 := ![first,second,third]
  let product := determinantMultilinear.restrictScalars ℝ
  have tuple := hasDerivAt_pi.mpr (fun slot : Fin 3 => originalCoreAxial_hasDerivAt parameters (fields slot) point angle)
  have derivative := (product.hasFDerivAt _).comp_hasDerivAt angle tuple
  have same : (fun time => coreValue (determinantOperation parameters first second third) point time)=
      (fun time => product (fun slot => coreValue (fields slot) point time)) := by
    funext time
    rw [originalDeterminant_value]
    rfl
  have original := originalCoreAxial_hasDerivAt parameters (determinantOperation parameters first second third) point angle
  rw [same] at original
  have value := original.unique derivative
  simp only [ContinuousMultilinearMap.linearDeriv_apply,Fin.sum_univ_three] at value
  simp only [fields,Matrix.cons_val] at value
  rw [coreValue_add,coreValue_add,originalDeterminant_value,originalDeterminant_value,originalDeterminant_value]
  convert value using 1
  rfl

end Grad.OriginalKernelHomogeneousGraph
