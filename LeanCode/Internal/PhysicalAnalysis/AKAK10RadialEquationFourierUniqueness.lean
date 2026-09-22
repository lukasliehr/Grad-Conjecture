import AKAK9SameScalarPhysicalCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.BoundaryTrace Grad.SourceCollarFullSource

/-- Absolute coefficient summability gives continuity of the exact physical
series by the existing uniform Fourier bound. -/
theorem physicalCharacterSeries_continuous (values : (ℤ × ℤ) → ComplexEuclidean 1)
    (summable : Summable (fun mode => ‖values mode‖)) : Continuous (physicalCharacterSeries values) := by
  have terms (mode : ℤ × ℤ) : Continuous (fun angles : ℝ × ℝ =>
      (cellExponential mode.1 angles.1 * cellExponential mode.2 angles.2) • values mode) := by
    exact (((cellExponential_smooth mode.1).continuous.comp continuous_fst).mul
      ((cellExponential_smooth mode.2).continuous.comp continuous_snd)).smul continuous_const
  exact continuous_tsum terms summable (fun mode angles => by
    simp only [norm_smul,norm_mul,cellExponential_norm,one_mul,le_refl])

/-- The existing all-grade radial jets supply the exact derivative series;
actual Fourier coefficients identify any literal continuous periodic RHS.
No additional summability or differentiability premise is imposed on the slope. -/
theorem hilbertPhysicalField_radial_of_doubleCoefficients
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
      curve grade radius mode = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (slope : (ℤ × ℤ) → ComplexEuclidean 1)
    (derivatives : ∀ mode, HasDerivWithinAt (fun current => curve 0 current mode) (slope mode) (Icc lower 1) radius)
    (rhs : ℝ × ℝ → ComplexEuclidean 1) (continuousRHS : Continuous rhs)
    (angular : ∀ axial, Function.Periodic (fun polar => rhs (polar,axial)) (2 * Real.pi))
    (cell : ∀ polar, Function.Periodic (fun axial => rhs (polar,axial)) (2 * Real.pi))
    (coefficients : ∀ mode, doubleCoefficient rhs mode = slope mode) (angles : ℝ × ℝ) :
    HasDerivWithinAt (fun current => hilbertPhysicalField lower bounded curve (current,angles))
      (rhs angles) (Icc lower 1) radius := by
  have sectionSame (mode : ℤ × ℤ) :
      hilbertRadialJetSection lower bounded curve smooth 1 0 mode ⟨radius,inside⟩ = slope mode := by
    have jet := hilbertRadialJetSection_derivative lower bounded curve smooth 0 0 mode radius inside
    simp only [iteratedDerivWithin_zero,Nat.zero_add] at jet
    exact (jet.derivWithin (uniqueDiffOn_Icc bounded radius inside)).symm.trans
      ((derivatives mode).derivWithin (uniqueDiffOn_Icc bounded radius inside))
  have sectionSummable : Summable (fun mode : ℤ × ℤ => ‖hilbertRadialJetSection lower bounded curve smooth 1 0 mode‖) := by
    simpa only [pow_zero,one_mul] using hilbertRadialJetSection_weighted_summable lower bounded curve smooth same 1 0
  have summable : Summable (fun mode => ‖slope mode‖) := by
    apply Summable.of_nonneg_of_le (fun mode => norm_nonneg _) (fun mode => ?_) sectionSummable
    rw [← sectionSame mode]
    exact (hilbertRadialJetSection lower bounded curve smooth 1 0 mode).norm_coe_le_norm ⟨radius,inside⟩
  have identical : physicalCharacterSeries slope = rhs := by
    apply doubleFourier_ext _ _ (physicalCharacterSeries_continuous slope summable) continuousRHS
      (physicalCharacterSeries_angular_periodic slope) angular
      (physicalCharacterSeries_cell_periodic slope) cell
    intro mode
    rw [physicalCharacterSeries_coefficient slope summable mode,← doubleCoefficient_swap rhs continuousRHS]
    exact (coefficients mode).symm
  have derivative := hilbertPhysicalField_radial_of_coefficients lower positive bounded curve smooth same radius inside slope derivatives angles
  rw [identical] at derivative
  exact derivative

end Grad.ActualPolarEquations
