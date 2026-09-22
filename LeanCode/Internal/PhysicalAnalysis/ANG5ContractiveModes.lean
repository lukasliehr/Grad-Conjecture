import ANG4AngularRowIntegral

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] diskComplexNormedSpace

/-- Angular averaging is contractive for the coupled Cartesian H1 row. -/
theorem angularRow_contract (mode : ℤ) (field : ClosedJet 1) :
    ‖apRowLinear (grade := 1) 1 0 0 1 0 (angularClosedJet mode field)‖ ≤
      ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ := by
  have positive : 0 < 2 * Real.pi := by positivity
  have mass : volume.real (Icc (0 : ℝ) (2 * Real.pi)) = 2 * Real.pi := by
    simp [Measure.real, Real.volume_Icc, Real.pi_pos.le]
  have bound : ‖∫ angle in Icc (0 : ℝ) (2 * Real.pi), unitAngularRow mode field angle‖ ≤
      (2 * Real.pi) * ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ := by
    calc
      _ ≤ ∫ angle in Icc (0 : ℝ) (2 * Real.pi), ‖unitAngularRow mode field angle‖ :=
        norm_integral_le_integral_norm _
      _ = _ := by simp_rw [unitAngularRow_norm]; rw [setIntegral_const]; change volume.real _ * _ = _; rw [mass]
  rw [angularRow_integral, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi) * ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖) :=
      mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr positive.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]

theorem diskCore_norm_row (field : ClosedJet 1) :
    ‖diskCoreInto field‖ = ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ := by
  change ‖apFiniteEmbed (grade := 1) 1 0 0 1 (Finsupp.single 0 field)‖ = _
  rw [apFiniteEmbed_single]
  change ‖(lp.single 2 0 (apRowLinear (grade := 1) 1 0 0 1 0 field) : APAmbient 1 1)‖ = _
  rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

/-- Norm-one angular projectors on the actual full-disk H1 completion. -/
theorem diskAngularMode_contract (mode : ℤ) (field : diskGrade) :
    ‖diskAngularMode mode field‖ ≤ ‖field‖ := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_le ((diskAngularMode mode).continuous.norm) continuous_norm) _ field
  intro core
  change ‖diskAngularMode mode (diskCoreInto core)‖ ≤ ‖diskCoreInto core‖
  rw [diskAngularMode_core, diskCore_norm_row, diskCore_norm_row]
  exact angularRow_contract mode core

theorem highDiskMode_contract (mode : ℤ) (field : highDiskGrade) :
    ‖highDiskMode mode field‖ ≤ ‖field‖ :=
  diskAngularMode_contract mode field.val

end Grad.CircularHighWeak
