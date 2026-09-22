import ANR52ActualClosedCollarConsumer

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Collective Bessel control on every finite angular set, with a
constant independent of the set and its largest frequency. -/
theorem diskPolar_finite_coefficient_energy (field : ClosedJet 1) (radial : ℕ) (upper : radial ≤ 1)
    (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode) ≤
      ((2 * Real.pi)⁻¹ * polarOrderConstant radial) * ‖diskCoreInto field‖ ^ 2 := by
  have bessel := annular_angular_bessel lower nonnegative bounded 0
    (radialIter radial (originalPolarValue field))
    (radialIter_smooth radial _ (originalPolarValue_smooth field))
    (radialIter_periodic radial _ (originalPolarValue_periodic field)) modes
  have finite : (∑ mode ∈ modes, annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode) ≤
      (2 * Real.pi)⁻¹ * annularIntegral lower (fun point => ‖radialIter radial (originalPolarValue field) point‖ ^ 2) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul, angularJet_zero] using bessel
  exact finite.trans ((mul_le_mul_of_nonneg_left (diskPolar_energy field radial upper lower nonnegative bounded)
    (by positivity)).trans_eq (mul_assoc _ _ _).symm)

theorem diskRadialBound_sq : diskRadialBound ^ 2 =
    (2 * Real.pi)⁻¹ * (polarOrderConstant 0 + polarOrderConstant 1) :=
  Real.sq_sqrt (mul_nonneg (by positivity)
    (add_nonneg (polarOrderConstant_nonnegative 0) (polarOrderConstant_nonnegative 1)))

theorem diskRadialCore_finite_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : ClosedJet 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, ‖diskRadialCore lower positive mode field‖ ^ 2) ≤
      diskRadialBound ^ 2 * ‖diskCoreInto field‖ ^ 2 := by
  have value := diskPolar_finite_coefficient_energy field 0 (by omega) lower positive.le bounded modes
  have slope := diskPolar_finite_coefficient_energy field 1 le_rfl lower positive.le bounded modes
  have equality : (∑ mode ∈ modes, ‖diskRadialCore lower positive mode field‖ ^ 2) =
      (∑ mode ∈ modes, annularCoefficientEnergy lower (radialIter 0 (originalPolarValue field)) mode) +
      (∑ mode ∈ modes, annularCoefficientEnergy lower (radialIter 1 (originalPolarValue field)) mode) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun mode _ => diskRadialCore_norm_sq lower positive bounded mode field)
  rw [equality, diskRadialBound_sq]
  nlinarith

/-- The same collective estimate extends to every actual disk H1 field
by density, without restricting the field to finitely many modes. -/
theorem diskRadial_finite_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : diskGrade) (modes : Finset ℤ) :
    (∑ mode ∈ modes, ‖diskRadial lower positive bounded mode field‖ ^ 2) ≤
      diskRadialBound ^ 2 * ‖field‖ ^ 2 := by
  have leftContinuous : Continuous (fun field : diskGrade =>
      ∑ mode ∈ modes, ‖diskRadial lower positive bounded mode field‖ ^ 2) :=
    continuous_finsetSum modes (fun mode _ => (diskRadial lower positive bounded mode).continuous.norm.pow 2)
  have rightContinuous : Continuous (fun field : diskGrade => diskRadialBound ^ 2 * ‖field‖ ^ 2) :=
    (continuous_norm.pow 2).const_mul (diskRadialBound ^ 2)
  apply isClosed_property diskCoreInto_denseRange (isClosed_le leftContinuous rightContinuous) _ field
  intro core
  have equality : (∑ mode ∈ modes, ‖diskRadial lower positive bounded mode (diskCoreInto core)‖ ^ 2) =
      ∑ mode ∈ modes, ‖diskRadialCore lower positive mode core‖ ^ 2 :=
    Finset.sum_congr rfl (fun mode _ => congrArg (fun radial : WeightedRadialH1 1 lower => ‖radial‖ ^ 2)
      (diskRadial_core lower positive bounded mode core))
  exact equality.trans_le (diskRadialCore_finite_energy lower positive bounded core modes)

theorem diskRadial_summable_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : diskGrade) : Summable (fun mode : ℤ => ‖diskRadial lower positive bounded mode field‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (diskRadial_finite_energy lower positive bounded field)

theorem diskRadial_total_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : diskGrade) :
    (∑' mode : ℤ, ‖diskRadial lower positive bounded mode field‖ ^ 2) ≤ diskRadialBound ^ 2 * ‖field‖ ^ 2 :=
  (diskRadial_summable_energy lower positive bounded field).tsum_le_of_sum_le
    (diskRadial_finite_energy lower positive bounded field)

end Grad.CircularHighRegularity
