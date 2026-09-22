import ACP8ActualForceCoefficients

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.ActualCurrentPrimitives
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation

def forceScalar (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ℂ :=
  forceFourier parameters L rho epsilon field kind low component radial radius mode 0

theorem forceScalar_continuous (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (mode : ℤ × ℤ) :
    Continuous (fun radius => forceScalar parameters L rho epsilon field kind low component radial radius mode) := by
  have continuousVector : Continuous (fun radius => forceFourier parameters L rho epsilon field kind low component radial radius mode) :=
    continuous_iff_continuousAt.mpr (fun radius =>
      (forceFourier_hasDerivAt parameters L rho epsilon field kind low component mode radial radius).continuousAt)
  exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp continuousVector

theorem forceScalarMoment_le (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    productMoment parameters tangential radius (forceScalar parameters L rho epsilon field kind low component radial radius) mode ≤
      polarFourierMass parameters tangential radius (forceFourier parameters L rho epsilon field kind low component radial radius) mode :=
  mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ 0)
    (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le (pow_nonneg (annularFrequency_nonnegative _ _) _))

theorem forceScalarMoment_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (forceScalar parameters L rho epsilon field kind low component radial radius)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (forceScalarMoment_le parameters L rho epsilon field kind low component tangential radial radius)
    (forceFourier_summable parameters L rho epsilon field kind low tangential radial component radius nonnegative bounded)

theorem forceScalarMoment_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, productMoment parameters tangential radius (forceScalar parameters L rho epsilon field kind low component radial radius) mode ≤
      forceFourierConstant parameters L kind tangential radial * physicalBudget parameters field rho epsilon (tangential + radial + 6) :=
  ((forceScalarMoment_summable parameters L rho epsilon field kind low component tangential radial radius nonnegative bounded).tsum_le_tsum
    (forceScalarMoment_le parameters L rho epsilon field kind low component tangential radial radius)
    (forceFourier_summable parameters L rho epsilon field kind low tangential radial component radius nonnegative bounded)).trans
    (forceFourier_bound parameters L rho epsilon field kind low tangential radial component radius nonnegative bounded)

end Grad.ActualCurrentPrimitives

