import AKBU14ActualPhysicalCovariantZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.SourceCollarFullSource
open Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField Grad.OriginalKernelCovariantRecovery

theorem originalCurve_traceZero_fullField {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {positive : 0<lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : Icc lower (1:ℝ)) (zero : originalCurveNegativeTrace curves radius=0) (angles : ℝ×ℝ) :
    curves.fullField bounded (radius.val,angles)=0 := by
  have equality := curves.fullField_eq_of_doubleCoefficient bounded radius.val radius.property
    (fun _ => 0) continuous_const (fun _ _ => rfl) (fun _ _ => rfl) (fun mode => by
      rw [←curves.fullField_doubleCoefficient bounded radius.val radius.property mode,
        ←originalCurveNegativeTrace_coefficient curves bounded radius mode,zero]
      simp only [doubleCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]
      exact (negativeTraceCoefficientCLM _ 0 0 mode).map_zero.symm)
  exact congrFun equality angles

end Grad.OriginalPhysicalKernelUniqueness
