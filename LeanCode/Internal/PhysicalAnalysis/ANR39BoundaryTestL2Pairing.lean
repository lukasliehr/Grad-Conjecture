import ANR36BoundaryCharacterTests

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarSupport_away (lower : ℝ) (positive : 0 < lower) (test : ℝ → ℝ)
    (supported : tsupport test ⊆ Ioi lower) : (0 : ℝ) ∉ tsupport test :=
  fun member => (not_lt_of_ge positive.le) (supported member)

private theorem boundaryTest_integral_restrict (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (test : ℝ → ℝ) (continuousTest : Continuous test) (supported : tsupport test ⊆ Ioi lower)
    (field : ℝ → ℂ) (continuousField : Continuous field) :
    (∫ radius in Icc (0 : ℝ) 1, (radius * test radius) • field radius) =
      ∫ radius in lower..1, (radius * test radius) • field radius := by
  have continuousIntegrand : Continuous (fun radius => (radius * test radius) • field radius) :=
    (continuous_id.mul continuousTest).smul continuousField
  have zeroInitial : (∫ radius in (0 : ℝ)..lower, (radius * test radius) • field radius) = 0 := by
    rw [intervalIntegral.integral_of_le positive.le]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    have zero : test radius = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro member
      exact (not_lt_of_ge inside.2) (supported member)
    simp only [zero, mul_zero, zero_smul, Pi.zero_apply]
  have split := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuousIntegrand.intervalIntegrable (0 : ℝ) lower) (continuousIntegrand.intervalIntegrable lower 1)
  rw [zeroInitial, zero_add] at split
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (positive.le.trans bounded)]
  exact split.symm

theorem boundaryCharacterJet_pairing (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (supported : tsupport test ⊆ Ioi lower) (field : DiskL2 1) :
    inner ℂ (closedL2Core (boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported))) field =
      (2 * Real.pi) • radialPairing lower positive (fun radius => radius * test radius)
        (continuous_id.mul smooth.continuous) vector (diskL2Radial lower positive bounded mode field) := by
  let jet := boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported)
  let pairing := radialPairing lower positive (fun radius => radius * test radius) (continuous_id.mul smooth.continuous) vector
  have sourceContinuous : Continuous (fun field : DiskL2 1 => inner ℂ (closedL2Core jet) field) :=
    (innerSL ℂ (closedL2Core jet)).continuous
  have targetContinuous : Continuous (fun field : DiskL2 1 => (2 * Real.pi) • pairing
      (diskL2Radial lower positive bounded mode field)) :=
    (pairing.continuous.comp (diskL2Radial lower positive bounded mode).continuous).const_smul (2 * Real.pi : ℝ)
  apply isClosed_property closedL2Core_denseRange (isClosed_eq sourceContinuous targetContinuous) _ field
  intro core
  have coreLaw := boundaryCharacterJet_core_pairing mode vector test smooth (collarSupport_away lower positive test supported) core
  have restriction := boundaryTest_integral_restrict lower positive bounded test smooth.continuous supported
    (fun radius => inner ℂ vector (radialCoefficientJet (originalPolarValue core) mode 0 radius))
    ((innerSL ℂ vector).continuous.comp (radialCoefficientJet_smooth _ (originalPolarValue_smooth core) mode 0).continuous)
  have literal := radialPairing_literal lower positive bounded (fun radius => radius * test radius)
    (continuous_id.mul smooth.continuous) vector (radialCoefficientJet (originalPolarValue core) mode 0)
    (radialCoefficientJet_smooth _ (originalPolarValue_smooth core) mode 0).continuous
  exact coreLaw.trans ((congrArg (fun value : ℂ => (2 * Real.pi) • value) restriction).trans
    ((congrArg (fun value : ℂ => (2 * Real.pi) • value) literal.symm).trans
      (congrArg (fun value : RadialL2 1 lower => (2 * Real.pi) • pairing value)
        (diskL2Radial_core lower positive bounded mode core).symm)))

theorem boundaryCharacterJet_ordinary (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (supported : tsupport test ⊆ Ioi lower) (field : DiskL2 1) :
    inner ℂ (closedL2Core (boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported))) field =
      (2 * Real.pi) • collarPairing lower ⟨fun radius => radius * test radius, continuous_id.mul smooth.continuous⟩
        vector (radialOrdinary 1 lower positive (diskL2Radial lower positive bounded mode field)) :=
  (boundaryCharacterJet_pairing lower positive bounded mode vector test smooth supported field).trans
    (congrArg (fun value : ℂ => (2 * Real.pi) • value)
      (radialPairing_ordinary 1 lower positive
        ⟨fun radius => radius * test radius, continuous_id.mul smooth.continuous⟩ vector _))

end Grad.CircularHighRegularity
