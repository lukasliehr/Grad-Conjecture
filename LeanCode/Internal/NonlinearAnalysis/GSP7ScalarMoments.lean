import GSP6PhysicalPolarCoefficients

noncomputable section
open scoped BigOperators
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCurrentPrimitives

def polarEntryScalar (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ℂ :=
  polarEntryFourier parameters family coherent row column radial radius mode 0

theorem polarEntryScalar_hasDerivAt (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    HasDerivAt (fun radius => polarEntryScalar parameters family coherent row column radial radius mode)
      (polarEntryScalar parameters family coherent row column (radial + 1) radius mode) radius :=
  ((PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : PhysicalValue 1 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (polarEntryFourier_hasDerivAt parameters family coherent row column mode radial radius)

theorem polarEntryScalarMoment_le (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    productMoment parameters tangential radius (polarEntryScalar parameters family coherent row column radial radius) mode ≤
      polarFourierMass parameters tangential radius (polarEntryFourier parameters family coherent row column radial radius) mode :=
  mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ 0)
    (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le (pow_nonneg (annularFrequency_nonnegative _ _) _))

theorem polarEntryScalarMoment_summable (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (polarEntryScalar parameters family coherent row column radial radius)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (polarEntryScalarMoment_le parameters family coherent row column tangential radial radius)
    (polarEntryFourier_summable parameters family coherent row column tangential radial radius nonnegative bounded)

theorem polarEntryScalarMoment_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, productMoment parameters tangential radius (polarEntryScalar parameters family coherent row column radial radius) mode ≤
      polarEntryConstant row column tangential radial * ‖family (tangential + radial + 1)‖ :=
  ((polarEntryScalarMoment_summable parameters family coherent row column tangential radial radius nonnegative bounded).tsum_le_tsum
    (polarEntryScalarMoment_le parameters family coherent row column tangential radial radius)
    (polarEntryFourier_summable parameters family coherent row column tangential radial radius nonnegative bounded)).trans
    (polarEntryFourier_bound parameters family coherent row column tangential radial radius nonnegative bounded)

theorem rotatedPolarEntryScalarMoment_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius
      (angularCoefficientSequence (polarEntryScalar parameters family coherent row column radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius
      (angularCoefficientSequence (polarEntryScalar parameters family coherent row column radial radius)) mode) ≤
      polarEntryConstant row column (tangential + 1) radial * ‖family (tangential + 1 + radial + 1)‖ := by
  have summable := polarEntryScalarMoment_summable parameters family coherent row column (tangential + 1) radial radius nonnegative bounded
  refine ⟨angularCoefficientSequence_moment_summable parameters tangential radius _ summable, ?_⟩
  apply (angularCoefficientSequence_moment_bound parameters tangential radius _ summable).trans
  exact polarEntryScalarMoment_bound parameters family coherent row column (tangential + 1) radial radius nonnegative bounded

end Grad.ActualGaugeSigmaPrimitives
