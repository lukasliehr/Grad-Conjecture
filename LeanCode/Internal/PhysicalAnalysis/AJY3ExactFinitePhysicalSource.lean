import AJY1ExactAngularPrimitiveCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularSmoothSources Grad.AnnularCurrentLow
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.SourceCollarAngular

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {field : DivisionRow 1 lower} (source : FiniteSmoothStoredRow lower field)

theorem finiteSourcePolynomial_grade (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    source.physicalPolynomial parameters grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        source.physicalPolynomial parameters 0 radius mode := by
  rw [source.physicalPolynomial_mode,source.physicalPolynomial_mode]
  simp only [pow_zero,one_smul]
  norm_cast

/-- Actual finite copied-source Fourier field, with the original physical
storage inverse and the original mode carrier. -/
def finiteSourcePhysicalField : (ℝ × (ℝ × ℝ)) → ComplexEuclidean 1 :=
  hilbertPhysicalField lower bounded (source.physicalPolynomial parameters)

include positive in
theorem finiteSourcePhysicalField_smooth_closed :
    ContDiffOn ℝ ∞ (finiteSourcePhysicalField parameters lower bounded source) (annularJointClosed lower) :=
  hilbertPhysicalField_smooth_closed lower positive bounded (source.physicalPolynomial parameters)
    (source.physicalPolynomial_smooth parameters positive)
    (fun grade radius _ mode => finiteSourcePolynomial_grade parameters lower source grade radius mode)

include positive in
theorem finiteSourcePhysicalField_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => finiteSourcePhysicalField parameters lower bounded source (radius, polar, axial)) mode.1) mode.2 =
      source.physicalPolynomial parameters 0 radius mode :=
  hilbertPhysicalField_coefficient lower bounded (source.physicalPolynomial parameters)
    (source.physicalPolynomial_smooth parameters positive)
    (fun grade point _ query => finiteSourcePolynomial_grade parameters lower source grade point query)
    radius inside mode

theorem finiteSourcePhysicalField_angular_periodic (radius axial : ℝ) :
    Function.Periodic
      (fun polar => finiteSourcePhysicalField parameters lower bounded source (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_angular_periodic lower bounded (source.physicalPolynomial parameters) radius axial

theorem finiteSourcePhysicalField_cell_periodic (radius polar : ℝ) :
    Function.Periodic
      (fun axial => finiteSourcePhysicalField parameters lower bounded source (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_cell_periodic lower bounded (source.physicalPolynomial parameters) radius polar

/-- Exact AE recovery of the already existing source row, rather than a
newly prescribed coefficient family. -/
theorem finiteSourcePhysicalField_actual :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode,
      angularCoefficient (fun axial => angularCoefficient
        (fun polar => finiteSourcePhysicalField parameters lower bounded source (radius, polar, axial)) mode.1) mode.2 =
        lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  filter_upwards [source.physicalPolynomial_actual parameters positive 0,
    ae_restrict_mem measurableSet_Icc] with radius actual inside
  intro mode
  rw [finiteSourcePhysicalField_coefficient parameters lower positive bounded source radius inside mode,
    actual mode]
  simp only [pow_zero,one_smul]

end Grad.AnnularPhysicalFourier
