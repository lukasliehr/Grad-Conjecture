import ACE1PowerDilationIntegral

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct Grad.RepresentedKernel.SpatialProduct

theorem powerDilationJet_smul {dimension : ℕ} (power : ℕ) (scalar : ℂ) (field : ClosedJet dimension) :
    powerDilationJet power (scalar • field) = scalar • powerDilationJet power field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (∫ scale in Icc (0 : ℝ) 1, scale ^ power • smoothClosedExtension (scalar • field) (scale • point.val)) =
    scalar • ∫ scale in Icc (0 : ℝ) 1, scale ^ power • smoothClosedExtension field (scale • point.val)
  rw [← integral_smul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  dsimp only
  have original := smoothClosedExtension_value field (dilationPoint scale inside.1 inside.2 point)
  have scaled := smoothClosedExtension_value (scalar • field) (dilationPoint scale inside.1 inside.2 point)
  have valueEquality : smoothClosedExtension (scalar • field) (scale • point.val) =
      scalar • smoothClosedExtension field (scale • point.val) :=
    scaled.trans (congrArg (fun value => scalar • value) original.symm)
  exact (congrArg (fun value => scale ^ power • value) valueEquality).trans (smul_comm _ _ _)

def powerDilationLinear (dimension power : ℕ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := powerDilationJet power
  map_add' := powerDilationJet_add power
  map_smul' := powerDilationJet_smul power

theorem powerDilationJet_zero (dimension power : ℕ) :
    powerDilationJet power (0 : ClosedJet dimension) = 0 :=
  (powerDilationLinear dimension power).map_zero

theorem unit_power_integral (power : ℕ) :
    (∫ scale in Icc (0 : ℝ) 1, scale ^ power) = 1 / (power + 1 : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  simp

/-- Exact positive compact-kernel derivative estimate, including scale zero. -/
theorem powerDilationJet_derivative_bound {dimension order : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (word : CartesianWord order) (bound : ℝ)
    (bounded : ∀ point : ClosedDisk, ‖closedDerivative field order word point‖ ≤ bound) (point : ClosedDisk) :
    ‖closedDerivative (powerDilationJet power field) order word point‖ ≤
      bound / (power + order + 1 : ℝ) := by
  rw [powerDilationJet_derivative]
  have domination : ∀ᵐ scale ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖scale ^ (power + order) • cartesianDerivative order word (smoothClosedExtension field) (scale • point.val)‖ ≤
        scale ^ (power + order) * bound := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with scale inside
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg inside.1 _)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg inside.1 _)
    exact (congrArg norm (smoothClosedExtension_derivative field word
      (dilationPoint scale inside.1 inside.2 point))).le.trans (bounded _)
  have integrableMajorant : IntegrableOn (fun scale : ℝ => scale ^ (power + order) * bound) (Icc 0 1) :=
    ((continuous_id.pow (power + order)).mul continuous_const).continuousOn.integrableOn_Icc
  have estimate := norm_integral_le_of_norm_le integrableMajorant domination
  rw [integral_mul_const, unit_power_integral] at estimate
  convert estimate using 1
  push_cast
  ring

theorem powerDilationJet_derivative_norm {dimension order : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (word : CartesianWord order) :
    ‖closedDerivative (powerDilationJet power field) order word‖ ≤
      ‖closedDerivative field order word‖ / (power + order + 1 : ℝ) := by
  apply (ContinuousMap.norm_le _ (div_nonneg (norm_nonneg _) (by positivity))).mpr
  intro point
  exact powerDilationJet_derivative_bound power field word _
    (fun point => ContinuousMap.norm_coe_le_norm _ point) point

end Grad.ActualCenterVolterra
