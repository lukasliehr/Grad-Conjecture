import SCC31ExactRadialProduct

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation

def kappaScalar (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ℂ :=
  kappaFourier parameters L rho epsilon field low component radial radius mode 0

theorem kappaScalar_continuous (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (mode : ℤ × ℤ) :
    Continuous (fun radius => kappaScalar parameters L rho epsilon field low component radial radius mode) := by
  have continuousVector : Continuous (fun radius => kappaFourier parameters L rho epsilon field low component radial radius mode) :=
    continuous_iff_continuousAt.mpr (fun radius =>
      (kappaFourier_hasDerivAt parameters L rho epsilon field low component mode radial radius).continuousAt)
  exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp continuousVector

theorem kappaScalarMoment_le (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    productMoment parameters tangential radius (kappaScalar parameters L rho epsilon field low component radial radius) mode ≤
      polarFourierMass parameters tangential radius (kappaFourier parameters L rho epsilon field low component radial radius) mode :=
  mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ 0)
    (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le (pow_nonneg (annularFrequency_nonnegative _ _) _))

theorem kappaScalarMoment_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (kappaScalar parameters L rho epsilon field low component radial radius)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (kappaScalarMoment_le parameters L rho epsilon field low component tangential radial radius)
    (kappaFourier_summable parameters L rho epsilon field low tangential radial component radius nonnegative bounded)

theorem kappaScalarMoment_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, productMoment parameters tangential radius (kappaScalar parameters L rho epsilon field low component radial radius) mode ≤
      kappaFourierConstant parameters L tangential radial * physicalBudget parameters field rho epsilon (tangential + radial + 5) :=
  ((kappaScalarMoment_summable parameters L rho epsilon field low component tangential radial radius nonnegative bounded).tsum_le_tsum
    (kappaScalarMoment_le parameters L rho epsilon field low component tangential radial radius)
    (kappaFourier_summable parameters L rho epsilon field low tangential radial component radius nonnegative bounded)).trans
    (kappaFourier_bound parameters L rho epsilon field low tangential radial component radius nonnegative bounded)

/-- Immediate exact completed-space consumer of BS40 and BS42, for every
genuine radial derivative of each actual signed-cofactor polar coefficient. -/
theorem actualKappaRadialProduct {dimension : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (power radial : ℕ) (lower : ℝ) (positive : 0 < lower)
    (high low : DivisionRow dimension lower) (compatible : RadialRowsCompatible lower power high low) :
    ∃ product : DivisionRow dimension lower,
      ‖product‖ ≤ productPhaseConstant parameters power *
        ((kappaFourierConstant parameters L 0 radial * physicalBudget parameters field rho epsilon (radial + 5)) * ‖high‖ +
          (kappaFourierConstant parameters L power radial * physicalBudget parameters field rho epsilon (power + radial + 5)) * ‖low‖) ∧
      (∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
        HasSum (fun shift : ℤ × ℤ => kappaScalar parameters L rho epsilon field small component radial radius shift •
          originalRowCoefficient parameters 0 lower low radius (mode - shift))
          (originalRowCoefficient parameters power lower product radius mode)) := by
  apply exactRadialProduct parameters power lower positive
    (kappaScalar parameters L rho epsilon field small component radial)
    (fun mode => (kappaScalar_continuous parameters L rho epsilon field small component radial mode).aestronglyMeasurable)
    _ _ (mul_nonneg (kappaFourierConstant_pos _ _ _ _).le (physicalBudget_nonnegative _ _ _ _ _))
    (mul_nonneg (kappaFourierConstant_pos _ _ _ _).le (physicalBudget_nonnegative _ _ _ _ _)) _ high low compatible
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  have nonnegative := (positive.trans_le inside.1).le
  refine ⟨kappaScalarMoment_summable parameters L rho epsilon field small component 0 radial radius nonnegative inside.2,
    kappaScalarMoment_summable parameters L rho epsilon field small component power radial radius nonnegative inside.2, ?_,
    kappaScalarMoment_bound parameters L rho epsilon field small component power radial radius nonnegative inside.2⟩
  simpa only [zero_add] using kappaScalarMoment_bound parameters L rho epsilon field small component 0 radial radius nonnegative inside.2

end Grad.SourceCollarCoefficients
