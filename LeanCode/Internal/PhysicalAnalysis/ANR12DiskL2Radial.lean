import ANR10RadialCore

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

private theorem closedL2_smooth_norm (field : ClosedJet 1) :
    (∫ point in closedUnitDisk, ‖smoothClosedExtension field point‖ ^ 2) = ‖closedL2Core field‖ ^ 2 := by
  have density := closedDerivative_density_integral field (0, 0)
  have diskMeasurable : MeasurableSet closedUnitDisk := by
    rw [closedUnitDisk_eq_closedBall]
    exact measurableSet_closedBall
  have densityEquality : (∫ point in closedUnitDisk, ‖smoothClosedExtension field point‖ ^ 2) =
      ∫ point in closedUnitDisk, ‖closedMultiDerivative field (0, 0) (ambientClosedDisk point)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem diskMeasurable] with point inside
    have ambient : ambientClosedDisk point = (⟨point, inside⟩ : ClosedDisk) := by
      apply Subtype.ext
      exact ambientClosedDisk_val_of_mem inside
    rw [closedMultiDerivative_zero, ambient, smoothClosedExtension_value field ⟨point, inside⟩]
  exact densityEquality.trans (density.trans (by
    change ‖closedContinuousToDiskL2 (closedMultiDerivative field (0, 0))‖ ^ 2 = _
    rw [closedMultiDerivative_zero]
    rfl))

theorem diskRadialCoefficientL2_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) :
    ‖diskRadialCoefficientL2 lower positive mode 0 field‖ ^ 2 ≤
      (2 * Real.pi)⁻¹ * ‖closedL2Core field‖ ^ 2 := by
  have bessel := annular_angular_bessel lower positive.le bounded 0 (originalPolarValue field)
    (originalPolarValue_smooth field) (originalPolarValue_periodic field) {mode}
  have single : annularCoefficientEnergy lower (originalPolarValue field) mode ≤
      (2 * Real.pi)⁻¹ * annularIntegral lower (fun point => ‖originalPolarValue field point‖ ^ 2) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul, Finset.sum_singleton, angularJet_zero] using bessel
  have area := annularIntegral_le_disk lower positive.le bounded
    (fun point => ‖smoothClosedExtension field point‖ ^ 2)
    ((smoothClosedExtension_smooth field).continuous.norm.pow 2) (fun _ => sq_nonneg _)
  have source := area.trans_eq (closedL2_smooth_norm field)
  have result := single.trans (mul_le_mul_of_nonneg_left source (by positivity))
  have coordinateNorm : ‖diskRadialCoefficientL2 lower positive mode 0 field‖ ^ 2 =
      annularCoefficientEnergy lower (originalPolarValue field) mode := by
    change ‖radialToLp lower (radialCoefficientJet (originalPolarValue field) mode 0)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode 0).continuous‖ ^ 2 = _
    rw [radialToLp_norm_sq lower positive.le bounded]
    rfl
  exact coordinateNorm.trans_le result

def diskRadialL2Bound : ℝ := Real.sqrt ((2 * Real.pi)⁻¹)

theorem diskRadialL2Bound_nonnegative : 0 ≤ diskRadialL2Bound := Real.sqrt_nonneg _

theorem diskRadialCoefficientL2_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) :
    ‖diskRadialCoefficientL2 lower positive mode 0 field‖ ≤ diskRadialL2Bound * ‖closedL2Core field‖ := by
  have energy := diskRadialCoefficientL2_energy lower positive bounded mode field
  have square : diskRadialL2Bound ^ 2 = (2 * Real.pi)⁻¹ := Real.sq_sqrt (by positivity)
  have nonnegative := mul_nonneg diskRadialL2Bound_nonnegative (norm_nonneg (closedL2Core field))
  nlinarith [sq_nonneg (‖diskRadialCoefficientL2 lower positive mode 0 field‖ -
    diskRadialL2Bound * ‖closedL2Core field‖)]

/-- Literal angular Fourier extraction on actual ordinary-area disk L2. -/
theorem diskL2Radial_exists (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    ∃ extraction : DiskL2 1 →L[ℂ] RadialL2 1 lower,
      (∀ field, extraction (closedL2Core field) = diskRadialCoefficientL2 lower positive mode 0 field) ∧
      (∀ field, ‖extraction field‖ ≤ diskRadialL2Bound * ‖field‖) :=
  apDense_extension closedL2Core closedL2Core_injective closedL2Core_denseRange
    (diskRadialCoefficientL2 lower positive mode 0) diskRadialL2Bound diskRadialL2Bound_nonnegative
    (diskRadialCoefficientL2_bound lower positive bounded mode)

def diskL2Radial (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ) :
    DiskL2 1 →L[ℂ] RadialL2 1 lower := (diskL2Radial_exists lower positive bounded mode).choose

theorem diskL2Radial_core (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ)
    (field : ClosedJet 1) :
    diskL2Radial lower positive bounded mode (closedL2Core field) = diskRadialCoefficientL2 lower positive mode 0 field :=
  (diskL2Radial_exists lower positive bounded mode).choose_spec.1 field

theorem diskL2Radial_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (mode : ℤ)
    (field : DiskL2 1) : ‖diskL2Radial lower positive bounded mode field‖ ≤ diskRadialL2Bound * ‖field‖ :=
  (diskL2Radial_exists lower positive bounded mode).choose_spec.2 field

end Grad.CircularHighRegularity
