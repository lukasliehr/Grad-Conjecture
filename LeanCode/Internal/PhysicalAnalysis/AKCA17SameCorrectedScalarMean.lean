import AKCA14NativeFullAngularMeans

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource Grad.BoundaryTrace Grad.AnnularCurrentLow Grad.AnnularCurrentEnergy

 theorem polarScalarOverRadius_zeroAngular (lower : ℝ) (xi : DivisionRow 1 lower) (polar : DivisionRow 3 lower)
    (zero : ∀ cell : ℤ,xi (0,cell)=0) (cell : ℤ) :
    polarScalarOverRadiusRow lower xi polar (0,cell)=0 := by
  change xi (0,cell)+meanFreeRow lower (bulkMatrixUnit lower (0 : Fin 1) (1 : Fin 3) polar) (0,cell)=0
  rw [zero,meanFreeRow_apply]
  simp

 theorem correctedScalarOverRadius_mean {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {xi : DivisionRow 1 lower} {polar : DivisionRow 3 lower}
    (scalar : SmoothLowPhysicalRow parameters lower positive xi)
    (covariant : SmoothLowPhysicalRow parameters lower positive polar) (bounded : lower<1)
    (zero : ∀ cell : ℤ,xi (0,cell)=0) (radius : ℝ) (inside : radius ∈ Icc lower 1) (axial : ℝ) :
    angularCoefficient (fun polar => (scalar.polarScalarOverRadius covariant).fullField bounded (radius,polar,axial)) 0=0 :=
  fullField_mean_of_zeroAngular (scalar.polarScalarOverRadius covariant) bounded
    (polarScalarOverRadius_zeroAngular lower xi polar zero) radius inside axial

 theorem correctedScalar_mean {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {xi : DivisionRow 1 lower} {polar : DivisionRow 3 lower}
    (scalar : SmoothLowPhysicalRow parameters lower positive xi)
    (covariant : SmoothLowPhysicalRow parameters lower positive polar) (bounded : lower<1)
    (zero : ∀ cell : ℤ,xi (0,cell)=0) (radius : ℝ) (inside : radius ∈ Icc lower 1) (axial : ℝ) :
    angularCoefficient (fun polar => radius • (scalar.polarScalarOverRadius covariant).fullField bounded (radius,polar,axial)) 0=0 := by
  have scalarLaw := angularCoefficient_valueMap ((radius : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 1))
    (fun polar => (scalar.polarScalarOverRadius covariant).fullField bounded (radius,polar,axial))
    (((scalar.polarScalarOverRadius covariant).fullField_continuous_angles bounded radius inside).comp
      (continuous_id.prodMk continuous_const)) 0
  change angularCoefficient (fun polar => (radius : ℂ) • (scalar.polarScalarOverRadius covariant).fullField bounded (radius,polar,axial)) 0=
    (radius : ℂ) • angularCoefficient (fun polar => (scalar.polarScalarOverRadius covariant).fullField bounded (radius,polar,axial)) 0 at scalarLaw
  simpa only [Complex.coe_smul,correctedScalarOverRadius_mean scalar covariant bounded zero radius inside axial,smul_zero] using scalarLaw

end Grad.OriginalCoreRealization
