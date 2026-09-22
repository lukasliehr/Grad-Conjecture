import AKAC7ActualVectorFourierReconstruction
import AJZ4FullOriginalBulkRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularWeightedSmoothness Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow
open Grad.AnnularPhysicalFourier Grad.AnnularRestriction Grad.AnnularSmoothCore Grad.AnnularSourceGraph

variable {dimension : ℕ} {parameters : PhaseParameters} {lower upper : ℝ}
    {positiveLower : 0 < lower} {positiveUpper : 0 < upper}
    {firstRow : DivisionRow dimension lower} {secondRow : DivisionRow dimension upper}
    (first : SmoothLowPhysicalRow parameters lower positiveLower firstRow)
    (second : SmoothLowPhysicalRow parameters upper positiveUpper secondRow)
    (lowerBounded : lower < 1) (upperBounded : upper < 1) (included : lower ≤ upper)
    (same : originalBulkRestriction dimension lower upper included firstRow = secondRow)

include same lowerBounded upperBounded

/-- Original common-rho restriction fixes every continuous physical Hilbert
curve pointwise, including the new collar endpoints. -/
theorem SmoothLowPhysicalRow.physicalCurve_restriction (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc upper 1) :
    first.physicalCurve grade radius = second.physicalCurve grade radius := by
  apply collarCurve_eq_of_ae upper upperBounded _ _
    ((first.physicalCurve_smooth lowerBounded grade).continuousOn.mono (Icc_subset_Icc_left included))
    (second.physicalCurve_smooth upperBounded grade).continuousOn _ inside
  filter_upwards [(first.physicalCurve_actual lowerBounded grade).filter_mono
      (ae_mono (collarMeasure_le lower upper included)),second.physicalCurve_actual upperBounded grade,
    originalBulkRestriction_lowRhoPhysical parameters dimension lower upper included positiveLower positiveUpper firstRow]
    with radius one two restricted
  apply lp.ext
  funext mode
  rw [one mode,two mode,← same,restricted mode]

theorem SmoothLowPhysicalRow.componentField_restriction (component : Fin dimension) (radius polar axial : ℝ)
    (inside : radius ∈ Icc upper 1) :
    first.componentField lowerBounded component (radius,polar,axial) =
      second.componentField upperBounded component (radius,polar,axial) := by
  have lowerInside : radius ∈ Icc lower 1 := ⟨included.trans inside.1,inside.2⟩
  unfold SmoothLowPhysicalRow.componentField hilbertPhysicalField
  rw [radialClamp_eq lower lowerBounded.le radius lowerInside,radialClamp_eq upper upperBounded.le radius inside]
  congr 1
  funext mode
  change physicalHilbertComponent parameters dimension component (first.physicalCurve 0 radius) mode =
    physicalHilbertComponent parameters dimension component (second.physicalCurve 0 radius) mode
  rw [first.physicalCurve_restriction second lowerBounded upperBounded included same 0 radius inside]

/-- The actual full physical vector agrees on overlapping collars; no new
representative or Fourier coefficient is chosen by restriction. -/
theorem SmoothLowPhysicalRow.fullField_restriction (radius polar axial : ℝ) (inside : radius ∈ Icc upper 1) :
    first.fullField lowerBounded (radius,polar,axial) = second.fullField upperBounded (radius,polar,axial) := by
  apply PiLp.ext
  intro component
  rw [first.fullField_coordinate,second.fullField_coordinate,
    first.componentField_restriction second lowerBounded upperBounded included same component radius polar axial inside]

end Grad.ActualSmoothPhysicalField
