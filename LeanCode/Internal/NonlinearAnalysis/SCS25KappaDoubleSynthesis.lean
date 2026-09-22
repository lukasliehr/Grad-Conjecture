import SCS24KappaAngularSynthesis

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryTrace Grad.SourceCollar Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

/-- The full double Fourier series reconstructs the actual physical signed
cofactor contraction at the original point, not a formal coefficient proxy. -/
theorem kappaScalar_double_hasSum (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius polarAngle axialAngle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun mode : ℤ × ℤ => fourierPhase mode.2 axialAngle *
      (cellExponential mode.1 polarAngle * kappaScalar parameters L rho epsilon field small component 0 radius mode))
      (physicalKappa polarAngle (originalPhysicalSignedCofactor parameters L epsilon field axialAngle
        (Grad.SourceCollarDivision.polarClosedPoint radius polarAngle nonnegative bounded)) component -
        (![0, -1, 0] : Fin 3 → ℂ) component) := by
  let term : ℤ × ℤ → ℂ := fun mode => fourierPhase mode.2 axialAngle *
    (cellExponential mode.1 polarAngle * kappaScalar parameters L rho epsilon field small component 0 radius mode)
  have norms : Summable (fun mode => ‖term mode‖) := by
    simpa only [term, norm_mul, fourierPhase_norm, cellExponential_norm, one_mul] using
      kappaScalar_norm_summable parameters L rho epsilon field small component radius nonnegative bounded
  have rotated : Summable (fun pair : ℤ × ℤ => term (pair.2, pair.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr norms.of_norm
  have equality : (∑' mode, term mode) =
      physicalKappa polarAngle (originalPhysicalSignedCofactor parameters L epsilon field axialAngle
        (Grad.SourceCollarDivision.polarClosedPoint radius polarAngle nonnegative bounded)) component -
        (![0, -1, 0] : Fin 3 → ℂ) component := by
    calc
      _ = ∑' pair : ℤ × ℤ, term (pair.2, pair.1) := ((Equiv.prodComm ℤ ℤ).tsum_eq term).symm
      _ = ∑' cell : ℤ, ∑' mode : ℤ, term (mode, cell) := rotated.tsum_prod
      _ = ∑' cell : ℤ, fourierPhase cell axialAngle *
          kappaPolarCell parameters L rho epsilon field small component cell (radius, polarAngle) 0 := by
        apply tsum_congr
        intro cell
        change (∑' mode : ℤ, fourierPhase cell axialAngle *
          (cellExponential mode polarAngle * kappaScalar parameters L rho epsilon field small component 0 radius (mode, cell))) = _
        rw [tsum_mul_left, (kappaScalar_angular_hasSum parameters L rho epsilon field small component radius nonnegative bounded cell polarAngle).tsum_eq]
      _ = _ := (kappaPolarCell_actual_fourier parameters L rho epsilon field small component radius polarAngle axialAngle nonnegative bounded).tsum_eq
  exact equality ▸ norms.of_norm.hasSum

end Grad.SourceCollarFullSource
