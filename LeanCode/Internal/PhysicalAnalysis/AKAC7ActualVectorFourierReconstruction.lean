import AKAC6ActualScalarFourierSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularWeightedSmoothness Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.BoundaryLift Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularPhysicalFourier
open Grad.AnnularClosedJointRegularity Grad.BoundaryTrace Grad.SourceCollarFullSource

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

/-- The genuine finite-dimensional physical field, assembled from the same
full two-frequency Fourier coefficients. -/
def SmoothLowPhysicalRow.fullField (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean dimension :=
  ∑ component : Fin dimension, matrixUnit component 0 (curves.componentField bounded component point)

theorem SmoothLowPhysicalRow.fullField_coordinate (point : ℝ × (ℝ × ℝ)) (component : Fin dimension) :
    curves.fullField bounded point component = curves.componentField bounded component point 0 := by
  simp [SmoothLowPhysicalRow.fullField,matrixUnit_apply,operatorBasis]

theorem SmoothLowPhysicalRow.fullField_smooth :
    ContDiffOn ℝ ∞ (curves.fullField bounded) (annularJointClosed lower) := by
  exact ContDiffOn.sum (fun component _ =>
    ((matrixUnit (input := 1) (output := dimension) component 0).restrictScalars ℝ).contDiff.comp_contDiffOn
      (curves.componentField_smooth bounded component))

theorem SmoothLowPhysicalRow.componentField_continuous_angles (component : Fin dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (fun angles : ℝ × ℝ => curves.componentField bounded component (radius,angles)) :=
  (curves.componentField_smooth bounded component).continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)

theorem SmoothLowPhysicalRow.fullField_continuous_angles (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (fun angles : ℝ × ℝ => curves.fullField bounded (radius,angles)) :=
  (curves.fullField_smooth bounded).continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)

/-- Two normalized Fourier integrals recover the original full vector,
with the common rho and phase removed only once. -/
theorem SmoothLowPhysicalRow.fullField_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => curves.fullField bounded (radius,polar,axial)) mode.1) mode.2 =
      curves.physicalCurve 0 radius mode := by
  have fullContinuous := curves.fullField_continuous_angles bounded radius inside
  have outerContinuous := Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter
    (fun angles : ℝ × ℝ => curves.fullField bounded (radius,angles.2,angles.1))
    (fullContinuous.comp continuous_swap) mode.1
  apply PiLp.ext
  intro component
  rw [angularCoefficient_component _ outerContinuous component]
  have inner (axial : ℝ) := angularCoefficient_component
    (fun polar => curves.fullField bounded (radius,polar,axial))
    (fullContinuous.comp (continuous_id.prodMk continuous_const)) component mode.1
  simp_rw [inner,curves.fullField_coordinate bounded]
  have scalarContinuous := curves.componentField_continuous_angles bounded component radius inside
  have scalarOuter := Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter
    (fun angles : ℝ × ℝ => curves.componentField bounded component (radius,angles.2,angles.1))
    (scalarContinuous.comp continuous_swap) mode.1
  have known := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (curves.componentField_coefficient bounded component radius inside mode)
  rw [angularCoefficient_component _ scalarOuter 0] at known
  have scalarInner (axial : ℝ) := angularCoefficient_component
    (fun polar => curves.componentField bounded component (radius,polar,axial))
    (scalarContinuous.comp (continuous_id.prodMk continuous_const)) 0 mode.1
  simp_rw [scalarInner] at known
  simpa [matrixUnit_apply,operatorBasis] using known

theorem SmoothLowPhysicalRow.fullField_actual :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      angularCoefficient (fun axial => angularCoefficient
        (fun polar => curves.fullField bounded (radius,polar,axial)) mode.1) mode.2 =
        lowRhoPhysicalCoefficient parameters lower positive row radius mode := by
  filter_upwards [curves.physicalCurve_actual bounded 0,ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  rw [curves.fullField_coefficient bounded radius inside mode,same mode,pow_zero,one_smul]

end Grad.ActualSmoothPhysicalField
