import AKAC5SameActualVectorCurves
import AKV40SamePhysicalFourierSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularWeightedSmoothness Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.BoundaryLift Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularPhysicalFourier
open Grad.AnnularClosedJointRegularity Grad.BoundaryTrace

def physicalHilbertComponent (parameters : PhaseParameters) (dimension : ℕ) (component : Fin dimension) :
    CellL2 dimension →L[ℂ] CellL2 1 :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit (input := dimension) (output := 1) 0 component)
    (norm_nonneg _) (fun _ => le_rfl)

theorem physicalHilbertComponent_apply (parameters : PhaseParameters) (dimension : ℕ) (component : Fin dimension)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    physicalHilbertComponent parameters dimension component field mode = matrixUnit 0 component (field mode) := rfl

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

def SmoothLowPhysicalRow.componentCurve (component : Fin dimension) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  physicalHilbertComponent parameters dimension component (curves.physicalCurve grade radius)

def SmoothLowPhysicalRow.componentField (component : Fin dimension) : ℝ × (ℝ × ℝ) → ComplexEuclidean 1 :=
  hilbertPhysicalField lower bounded (curves.componentCurve component)

include bounded

theorem SmoothLowPhysicalRow.componentCurve_smooth (component : Fin dimension) (grade : ℕ) :
    ContDiffOn ℝ ∞ (curves.componentCurve component grade) (Icc lower 1) :=
  ((physicalHilbertComponent parameters dimension component).restrictScalars ℝ).contDiff.comp_contDiffOn
    (curves.physicalCurve_smooth bounded grade)

theorem SmoothLowPhysicalRow.componentCurve_grade (component : Fin dimension) (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curves.componentCurve component grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        curves.componentCurve component 0 radius mode := by
  simp only [SmoothLowPhysicalRow.componentCurve,physicalHilbertComponent_apply,
    curves.physicalCurve_grade bounded grade radius inside mode,map_smul,Complex.ofReal_pow]
  rfl

theorem SmoothLowPhysicalRow.componentField_smooth (component : Fin dimension) :
    ContDiffOn ℝ ∞ (curves.componentField bounded component) (annularJointClosed lower) :=
  hilbertPhysicalField_smooth_closed lower positive bounded _
    (curves.componentCurve_smooth bounded component) (curves.componentCurve_grade bounded component)

theorem SmoothLowPhysicalRow.componentField_coefficient (component : Fin dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => curves.componentField bounded component (radius,polar,axial)) mode.1) mode.2 =
      matrixUnit 0 component (curves.physicalCurve 0 radius mode) :=
  hilbertPhysicalField_coefficient lower bounded _ (curves.componentCurve_smooth bounded component)
    (curves.componentCurve_grade bounded component) radius inside mode

theorem SmoothLowPhysicalRow.componentField_actual (component : Fin dimension) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      angularCoefficient (fun axial => angularCoefficient
        (fun polar => curves.componentField bounded component (radius,polar,axial)) mode.1) mode.2 =
        matrixUnit 0 component (lowRhoPhysicalCoefficient parameters lower positive row radius mode) := by
  filter_upwards [curves.physicalCurve_actual bounded 0,ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  rw [curves.componentField_coefficient bounded component radius inside mode,same mode,pow_zero,one_smul]

end Grad.ActualSmoothPhysicalField
