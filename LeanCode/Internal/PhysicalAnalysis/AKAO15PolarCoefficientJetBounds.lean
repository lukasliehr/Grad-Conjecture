import AKAO14SameOriginalPhysicalRVTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (coherent : FamilyCoherent family) (row component : Fin 3)

def polarScalarJetMajorant (rank : ℕ) (mode : ℤ × ℤ) : ℝ :=
  (polarEntryConstant row component 4 rank * ‖family (4+rank+1)‖) * (annularFrequency mode.1 mode.2 ^ 4)⁻¹

theorem polarScalarJetMajorant_summable (rank : ℕ) :
    Summable (polarScalarJetMajorant parameters family row component rank) :=
  fullLattice_decay_summable.mul_left _

/-- Existing analytic moments give a uniform summable radial-jet majorant at the original width. -/
theorem polarScalarJetMajorant_bound (rank : ℕ) (mode : ℤ × ℤ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ‖polarEntryScalar parameters family coherent row component rank radius mode‖ ≤
      polarScalarJetMajorant parameters family row component rank mode := by
  unfold polarScalarJetMajorant
  rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos (annularFrequency_pos mode) 4)]
  have term := (polarEntryScalarMoment_summable parameters family coherent row component 4 rank radius nonnegative bounded).le_tsum mode
    (fun other _ => productMoment_nonnegative parameters 4 radius _ other)
  have estimate := term.trans (polarEntryScalarMoment_bound parameters family coherent row component 4 rank radius nonnegative bounded)
  apply le_trans _ estimate
  change ‖polarEntryScalar parameters family coherent row component rank radius mode‖ * annularFrequency mode.1 mode.2 ^ 4 ≤
    coefficientRadialEnvelope parameters mode.2 radius * annularFrequency mode.1 mode.2 ^ 4 * ‖polarEntryScalar parameters family coherent row component rank radius mode‖
  have weighted := mul_le_mul_of_nonneg_right (coefficientRadialEnvelope_one_le parameters radius nonnegative bounded mode.2)
    (mul_nonneg (pow_nonneg (annularFrequency_pos mode).le 4) (norm_nonneg (polarEntryScalar parameters family coherent row component rank radius mode)))
  nlinarith only [weighted]

def polarRadialScalarSeries (rank : ℕ) (radius : ℝ) (angles : ℝ × ℝ) : ℂ :=
  ∑' mode : ℤ × ℤ,cellExponential mode.2 angles.2 *
    (cellExponential mode.1 angles.1 * polarEntryScalar parameters family coherent row component rank radius mode)

theorem polarRadialScalarSeries_zero (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angles : ℝ × ℝ) :
    polarRadialScalarSeries parameters family coherent row component 0 radius angles =
      polarFamilyAngleEntry parameters family row component radius nonnegative bounded angles :=
  (polarFamilyAngleEntry_eq_tsum parameters family coherent row radius nonnegative bounded component angles).symm

theorem polarRadialScalarSeries_hasSum (rank : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angles : ℝ × ℝ) :
    HasSum (fun mode : ℤ × ℤ => cellExponential mode.2 angles.2 *
      (cellExponential mode.1 angles.1 * polarEntryScalar parameters family coherent row component rank radius mode))
      (polarRadialScalarSeries parameters family coherent row component rank radius angles) := by
  apply Summable.hasSum
  apply Summable.of_norm_bounded (polarScalarJetMajorant_summable parameters family row component rank)
  intro mode
  simpa only [norm_mul,cellExponential_norm,one_mul] using
    polarScalarJetMajorant_bound parameters family coherent row component rank mode radius nonnegative bounded

end Grad.ActualPolarFlux
