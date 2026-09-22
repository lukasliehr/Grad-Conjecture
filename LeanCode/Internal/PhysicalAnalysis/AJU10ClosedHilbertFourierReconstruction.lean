import AJU9ExactFullFourierRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceCollarCoefficients Grad.AnnularJointRegularity Grad.AnnularRegularity
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.SourceCollarAngular

theorem physicalCharacterSeries_angular_periodic (values : (ℤ × ℤ) → ComplexEuclidean 1) (axial : ℝ) :
    Function.Periodic (fun polar => physicalCharacterSeries values (polar, axial)) (2 * Real.pi) := by
  intro polar
  unfold physicalCharacterSeries
  apply tsum_congr
  intro mode
  simp only [← cellCharacter_coe, AddCircle.coe_add_period]

theorem physicalCharacterSeries_cell_periodic (values : (ℤ × ℤ) → ComplexEuclidean 1) (polar : ℝ) :
    Function.Periodic (fun axial => physicalCharacterSeries values (polar, axial)) (2 * Real.pi) := by
  intro axial
  unfold physicalCharacterSeries
  apply tsum_congr
  intro mode
  simp only [← cellCharacter_coe, AddCircle.coe_add_period]

theorem physicalMixedFourierField_baseSeries (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : PhysicalFourierJet lower positive bounded) (radial : ℕ) (point : ℝ × (ℝ × ℝ)) :
    physicalMixedFourierField lower positive bounded jet radial 0 0 point =
      physicalCharacterSeries (fun mode => jet.sections radial mode (radialClamp lower bounded.le point.1)) point.2 := by
  rw [physicalMixedFourierField, physicalMixedFourierSection_apply]
  simp only [physicalCharacterSeries, physicalFourierCoefficient, physicalMixedSymbol, pow_zero, mul_one]

/-- The literal full physical Fourier field of the base Hilbert curve. Its
definition is independent of every smoothness witness and chosen higher grade. -/
def hilbertPhysicalField (lower : ℝ) (bounded : lower < 1) (curve : ℕ → ℝ → CellL2 1)
    (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean 1 :=
  physicalCharacterSeries (fun mode => curve 0 (radialClamp lower bounded.le point.1) mode) point.2

variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
      curve grade radius mode =
        ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode)

theorem hilbertPhysicalField_eq_jet :
    hilbertPhysicalField lower bounded curve =
      physicalMixedFourierField lower positive bounded (physicalJetOfHilbert lower positive bounded curve smooth same) 0 0 0 := by
  funext point
  rw [physicalMixedFourierField_baseSeries]
  simp only [physicalJetOfHilbert, hilbertRadialJetSection, iteratedDerivWithin_zero]
  rfl

include positive smooth same in
/-- All polynomial Hilbert curves of the SAME field supply genuine joint
smoothness on the literal closed collar, including both original endpoints. -/
theorem hilbertPhysicalField_smooth_closed :
    ContDiffOn ℝ ∞ (hilbertPhysicalField lower bounded curve) (annularJointClosed lower) := by
  rw [hilbertPhysicalField_eq_jet lower positive bounded curve smooth same]
  exact physicalMixedFourierField_smooth_closed lower positive bounded
    (physicalJetOfHilbert lower positive bounded curve smooth same) 0 0 0

include smooth same in
/-- The two actual normalized Fourier integrals recover the original full
Hilbert coefficient, retaining every high, low and zero mode exactly. -/
theorem hilbertPhysicalField_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => hilbertPhysicalField lower bounded curve (radius, polar, axial)) mode.1) mode.2 =
      curve 0 radius mode := by
  have sectionSummable : Summable (fun query : ℤ × ℤ =>
      ‖hilbertRadialJetSection lower bounded curve smooth 0 0 query‖) := by
    simpa only [pow_zero, one_mul] using
      hilbertRadialJetSection_weighted_summable lower bounded curve smooth same 0 0
  have summable : Summable (fun query : ℤ × ℤ => ‖curve 0 radius query‖) := by
    apply Summable.of_nonneg_of_le (fun query => norm_nonneg _) (fun query => ?_) sectionSummable
    exact (hilbertRadialJetSection lower bounded curve smooth 0 0 query).norm_coe_le_norm ⟨radius, inside⟩
  change angularCoefficient (fun axial => angularCoefficient
    (fun polar => physicalCharacterSeries
      (fun query => curve 0 (radialClamp lower bounded.le radius) query) (polar, axial)) mode.1) mode.2 = _
  rw [radialClamp_eq lower bounded.le radius inside]
  exact physicalCharacterSeries_coefficient (fun query => curve 0 radius query) summable mode

theorem hilbertPhysicalField_angular_periodic (radius axial : ℝ) :
    Function.Periodic (fun polar => hilbertPhysicalField lower bounded curve (radius, polar, axial)) (2 * Real.pi) := by
  exact physicalCharacterSeries_angular_periodic
    (fun mode => curve 0 (radialClamp lower bounded.le radius) mode) axial

theorem hilbertPhysicalField_cell_periodic (radius polar : ℝ) :
    Function.Periodic (fun axial => hilbertPhysicalField lower bounded curve (radius, polar, axial)) (2 * Real.pi) := by
  exact physicalCharacterSeries_cell_periodic
    (fun mode => curve 0 (radialClamp lower bounded.le radius) mode) polar

end Grad.AnnularPhysicalFourier
