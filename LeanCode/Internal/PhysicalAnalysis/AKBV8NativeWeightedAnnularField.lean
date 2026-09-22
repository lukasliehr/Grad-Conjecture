import AKBV7ClosedCylinderJet
import AKAC9PeriodicSameVectorField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularWeightedSmoothness Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.BoundaryLift Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularPhysicalFourier
open Grad.AnnularClosedJointRegularity Grad.BoundaryTrace Grad.SourceCollarFullSource

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

def weightedComponentCurve (component : Fin dimension) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  physicalHilbertComponent parameters dimension component (curves.curve grade radius)

def weightedComponentField (component : Fin dimension) : ℝ × (ℝ × ℝ) → ComplexEuclidean 1 :=
  hilbertPhysicalField lower bounded (weightedComponentCurve curves component)

include bounded

omit bounded in
theorem weightedComponentCurve_smooth (component : Fin dimension) (grade : ℕ) :
    ContDiffOn ℝ ∞ (weightedComponentCurve curves component grade) (Icc lower 1) :=
  ((physicalHilbertComponent parameters dimension component).restrictScalars ℝ).contDiff.comp_contDiffOn
    (curves.smooth grade)

theorem weightedComponentCurve_grade (component : Fin dimension) (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    weightedComponentCurve curves component grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        weightedComponentCurve curves component 0 radius mode := by
  have same := curves.shift bounded 0 grade radius inside mode
  simp only [zero_add] at same
  simp only [weightedComponentCurve,physicalHilbertComponent_apply,same,map_smul,Complex.ofReal_pow]
  rfl

theorem weightedComponentField_smooth (component : Fin dimension) :
    ContDiffOn ℝ ∞ (weightedComponentField curves bounded component) (annularJointClosed lower) :=
  hilbertPhysicalField_smooth_closed lower positive bounded _
    (weightedComponentCurve_smooth curves component) (weightedComponentCurve_grade curves bounded component)

theorem weightedComponentField_coefficient (component : Fin dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => weightedComponentField curves bounded component (radius,polar,axial)) mode.1) mode.2 =
      matrixUnit 0 component (curves.curve 0 radius mode) :=
  hilbertPhysicalField_coefficient lower bounded _ (weightedComponentCurve_smooth curves component)
    (weightedComponentCurve_grade curves bounded component) radius inside mode

/-- The weighted field is synthesized from the existing SAME native Hilbert curves; no phase estimate replaces the literal weight. -/
def weightedFullField (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean dimension :=
  ∑ component : Fin dimension, matrixUnit component 0 (weightedComponentField curves bounded component point)

theorem weightedFullField_coordinate (point : ℝ × (ℝ × ℝ)) (component : Fin dimension) :
    weightedFullField curves bounded point component = weightedComponentField curves bounded component point 0 := by
  simp [weightedFullField,matrixUnit_apply,operatorBasis]

theorem weightedFullField_smooth :
    ContDiffOn ℝ ∞ (weightedFullField curves bounded) (annularJointClosed lower) := by
  exact ContDiffOn.sum (fun component _ =>
    ((matrixUnit (input := 1) (output := dimension) component 0).restrictScalars ℝ).contDiff.comp_contDiffOn
      (weightedComponentField_smooth curves bounded component))

theorem weightedComponentField_continuous_angles (component : Fin dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (fun angles : ℝ × ℝ => weightedComponentField curves bounded component (radius,angles)) :=
  (weightedComponentField_smooth curves bounded component).continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)

theorem weightedFullField_continuous_angles (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (fun angles : ℝ × ℝ => weightedFullField curves bounded (radius,angles)) :=
  (weightedFullField_smooth curves bounded).continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)

/-- Two normalized Fourier integrals recover the exact native weighted coefficient, retaining every signed angular and axial mode. -/
theorem weightedFullField_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => weightedFullField curves bounded (radius,polar,axial)) mode.1) mode.2 =
      curves.curve 0 radius mode := by
  have fullContinuous := weightedFullField_continuous_angles curves bounded radius inside
  have outerContinuous := Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter
    (fun angles : ℝ × ℝ => weightedFullField curves bounded (radius,angles.2,angles.1))
    (fullContinuous.comp continuous_swap) mode.1
  apply PiLp.ext
  intro component
  rw [angularCoefficient_component _ outerContinuous component]
  have inner (axial : ℝ) := angularCoefficient_component
    (fun polar => weightedFullField curves bounded (radius,polar,axial))
    (fullContinuous.comp (continuous_id.prodMk continuous_const)) component mode.1
  simp_rw [inner,weightedFullField_coordinate curves bounded]
  have scalarContinuous := weightedComponentField_continuous_angles curves bounded component radius inside
  have scalarOuter := Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter
    (fun angles : ℝ × ℝ => weightedComponentField curves bounded component (radius,angles.2,angles.1))
    (scalarContinuous.comp continuous_swap) mode.1
  have known := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (weightedComponentField_coefficient curves bounded component radius inside mode)
  rw [angularCoefficient_component _ scalarOuter 0] at known
  have scalarInner (axial : ℝ) := angularCoefficient_component
    (fun polar => weightedComponentField curves bounded component (radius,polar,axial))
    (scalarContinuous.comp (continuous_id.prodMk continuous_const)) 0 mode.1
  simp_rw [scalarInner] at known
  simpa [matrixUnit_apply,operatorBasis] using known

theorem weightedFullField_angular_periodic (radius axial : ℝ) :
    Function.Periodic (fun polar => weightedFullField curves bounded (radius,polar,axial)) (2 * Real.pi) := by
  intro polar
  apply PiLp.ext
  intro component
  rw [weightedFullField_coordinate curves,weightedFullField_coordinate curves]
  exact congrArg (fun value : ComplexEuclidean 1 => value 0)
    (hilbertPhysicalField_angular_periodic lower bounded (weightedComponentCurve curves component) radius axial polar)

theorem weightedFullField_cell_periodic (radius polar : ℝ) :
    Function.Periodic (fun axial => weightedFullField curves bounded (radius,polar,axial)) (2 * Real.pi) := by
  intro axial
  apply PiLp.ext
  intro component
  rw [weightedFullField_coordinate curves,weightedFullField_coordinate curves]
  exact congrArg (fun value : ComplexEuclidean 1 => value 0)
    (hilbertPhysicalField_cell_periodic lower bounded (weightedComponentCurve curves component) radius polar axial)


end Grad.CartesianCoreRecovery
