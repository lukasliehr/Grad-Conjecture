import AKBM3SameOriginalSevenCovariant
import AKBD26SameCartesianSignedCofactorFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.ActualCartesianEquations
open Grad.OriginalKernelCovariantRecovery Grad.AnnularCurrentLow Grad.AnnularOriginalSmoothCore
open Grad.AnnularPhysicalReconstruction Grad.GaugeCoefficients.Physical.Ledger

/-- An exact negative Fourier angular derivative gives the genuine angular
derivative of the SAME smooth full field. -/
theorem originalSmoothCurve_angular_of_negative {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row rotated : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (rotation : SmoothLowPhysicalRow parameters lower positive rotated) (bounded : lower<1)
    (law : ∀ radius : Icc lower (1:ℝ),IsAngularDerivative _ 0 0
      (originalCurveNegativeTrace curves radius) (originalCurveNegativeTrace rotation radius))
    (radius : ℝ) (inside : radius∈Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => curves.fullField bounded (radius,angle,axial))
      (rotation.fullField bounded (radius,polar,axial)) polar := by
  apply samePhysical_angularDerivative curves rotation bounded _ radius inside polar axial
  filter_upwards [rotation.physicalCurve_actual bounded 0,curves.physicalCurve_actual bounded 0,
    ae_restrict_mem measurableSet_Icc] with location first second included
  intro mode
  have actual := law ⟨location,included⟩ mode
  rw [originalCurveNegativeTrace_coefficient rotation bounded ⟨location,included⟩,
    originalCurveNegativeTrace_coefficient curves bounded ⟨location,included⟩,
    rotation.fullField_doubleCoefficient bounded location included mode,
    curves.fullField_doubleCoefficient bounded location included mode,first mode,second mode] at actual
  simpa only [pow_zero,one_smul] using actual

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower} {row : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)

theorem originalDifferentiatedCurves_angular (radius : ℝ) (inside : radius∈Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => curves.fullField bounded (radius,angle,axial))
      ((originalDifferentiatedCurves curves bounded false).2.fullField bounded (radius,polar,axial)) polar := by
  apply originalSmoothCurve_angular_of_negative curves _ bounded _ radius inside polar axial
  intro query
  rw [originalDifferentiatedCurves_negativeRotation]
  exact originalCurveNegativeRotation_derivative curves bounded query

/-- Four genuine scalar curves give the exact full seven physical values. -/
theorem originalSmoothSevenCurves_fullField {pressureRow xiRow : DivisionRow 1 lower}
    (pressure : SmoothLowPhysicalRow parameters lower positive pressureRow)
    (xi : SmoothLowPhysicalRow parameters lower positive xiRow)
    (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    (originalSmoothSevenCurves pressure xi bounded).fullField bounded (radius,angles)=
      WithLp.toLp 2 ![(originalDifferentiatedCurves pressure bounded false).2.fullField bounded (radius,angles) 0,
        (radius:ℂ)⁻¹*((originalDifferentiatedCurves xi bounded false).2.fullField bounded (radius,angles) 0),
        (originalDifferentiatedCurves xi bounded true).2.fullField bounded (radius,angles) 0,
        (radius:ℂ)⁻¹*(xi.fullField bounded (radius,angles) 0),0,0,0] := by
  unfold originalSmoothSevenCurves
  simp only [SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    Grad.OriginalKernelGraphRestriction.originalInverseRadiusCurves_fullField lower positive _ bounded radius inside angles]
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [matrixUnit_apply,operatorBasis]

end Grad.OriginalKernelHomogeneousGraph
