import SCS36ContinuousFourier

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Algebra

variable (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
  (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3)

theorem physicalKappaDeviation_eq_tsum (angles : ℝ × ℝ) :
    physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component angles =
      ∑' mode : ℤ × ℤ, cellExponential mode.2 angles.2 *
        (cellExponential mode.1 angles.1 * kappaScalar parameters L rho epsilon field small component 0 radius mode) := by
  exact (kappaScalar_double_hasSum parameters L rho epsilon field small component radius angles.1 angles.2
    nonnegative bounded).tsum_eq.symm

include small in
theorem physicalKappaDeviation_continuous :
    Continuous (physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component) := by
  change Continuous (fun angles => physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component angles)
  simp_rw [physicalKappaDeviation_eq_tsum parameters L rho epsilon field small radius nonnegative bounded component]
  apply continuous_tsum
    (fun mode : ℤ × ℤ => ((cellExponential_smooth mode.2).continuous.comp continuous_snd).mul
      (((cellExponential_smooth mode.1).continuous.comp continuous_fst).mul continuous_const))
    (kappaScalar_norm_summable parameters L rho epsilon field small component radius nonnegative bounded)
  intro mode angles
  change ‖cellExponential mode.2 angles.2 * (cellExponential mode.1 angles.1 *
    kappaScalar parameters L rho epsilon field small component 0 radius mode)‖ ≤ _
  simp only [norm_mul, cellExponential_norm, one_mul, le_refl]

include small in
theorem physicalKappaDeviation_polar_periodic (axial : ℝ) :
    Function.Periodic (fun polar => physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component (polar, axial))
      (2 * Real.pi) := by
  intro polar
  change physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component (polar + 2 * Real.pi, axial) =
    physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component (polar, axial)
  rw [physicalKappaDeviation_eq_tsum parameters L rho epsilon field small,
    physicalKappaDeviation_eq_tsum parameters L rho epsilon field small]
  apply tsum_congr
  intro mode
  simp only [← cellCharacter_coe, AddCircle.coe_add_period]

end Grad.SourceCollarFullSource
