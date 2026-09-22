import AKAO16LiteralPolarRadialJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (row component : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (r : RadialPoint)

theorem cofactorJetScalar_norm_summable :
    Summable (fun mode => ‖radialCofactorJetScalar parameters length compact state row component radial direction r mode‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (radialCofactorJetScalar_moments parameters length compact state row component radial direction r 0)
  intro mode
  change ‖_‖ ≤ coefficientRadialEnvelope parameters mode.2 r.val * _^0 * ‖_‖
  simpa only [pow_zero,mul_one,one_mul] using mul_le_mul_of_nonneg_right
    (coefficientRadialEnvelope_one_le parameters r.val r.property.1 r.property.2 mode.2)
    (norm_nonneg (radialCofactorJetScalar parameters length compact state row component radial direction r mode))

def originalCofactorJetSeries (angles : ℝ × ℝ) : ℂ :=
  ∑' mode : ℤ × ℤ,cellExponential mode.2 angles.2 *
    (cellExponential mode.1 angles.1 * radialCofactorJetScalar parameters length compact state row component radial direction r mode)

theorem originalCofactorJetSeries_hasSum (angles : ℝ × ℝ) :
    HasSum (fun mode : ℤ × ℤ => cellExponential mode.2 angles.2 *
      (cellExponential mode.1 angles.1 * radialCofactorJetScalar parameters length compact state row component radial direction r mode))
      (originalCofactorJetSeries parameters length compact state row component radial direction r angles) := by
  apply Summable.hasSum
  apply Summable.of_norm_bounded (cofactorJetScalar_norm_summable parameters length compact state row component radial direction r)
  intro mode
  simp only [norm_mul,cellExponential_norm,one_mul,le_refl]

theorem originalCofactorJetSeries_continuous :
    Continuous (originalCofactorJetSeries parameters length compact state row component radial direction r) := by
  apply continuous_tsum
    (fun mode : ℤ × ℤ => ((cellExponential_smooth mode.2).continuous.comp continuous_snd).mul
      (((cellExponential_smooth mode.1).continuous.comp continuous_fst).mul continuous_const))
    (cofactorJetScalar_norm_summable parameters length compact state row component radial direction r)
  intro mode angles
  change ‖cellExponential mode.2 angles.2 * (cellExponential mode.1 angles.1 * radialCofactorJetScalar parameters length compact state row component radial direction r mode)‖ ≤ _
  simp only [norm_mul,cellExponential_norm,one_mul,le_refl]

theorem originalCofactorJetSeries_periodic (angles : ℝ × ℝ) :
    originalCofactorJetSeries parameters length compact state row component radial direction r (angles.1+2*Real.pi,angles.2) =
      originalCofactorJetSeries parameters length compact state row component radial direction r angles ∧
    originalCofactorJetSeries parameters length compact state row component radial direction r (angles.1,angles.2+2*Real.pi) =
      originalCofactorJetSeries parameters length compact state row component radial direction r angles := by
  constructor <;> apply tsum_congr <;> intro mode <;>
    simp only [← cellCharacter_coe,AddCircle.coe_add_period]

theorem originalCofactorJetSeries_radial (angles : ℝ × ℝ) :
    originalCofactorJetSeries parameters length compact state row component radial 0 r angles =
      polarRadialScalarSeries parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field)
        (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
        row component radial.val r.val angles := by
  apply tsum_congr
  intro mode
  simp only [radialCofactorJetScalar,cofactorJetSequence_zero]

theorem originalCofactorJetSeries_literal (angles : ℝ × ℝ) :
    originalCofactorJetSeries parameters length compact state row component 0 0 r angles =
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field row angles.2 angles.1
        (polarClosedPoint r.val angles.1 r.property.1 r.property.2) component + if row=component then 1 else 0 := by
  rw [originalCofactorJetSeries_radial parameters length compact state row component 0 r angles]
  simp only [Fin.val_zero]
  rw [polarRadialScalarSeries_zero parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field)
      (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
      row component r.val r.property.1 r.property.2 angles]
  simp only [polarFamilyAngleEntry,
    originalCofactorDeviation_matrix parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    polarMatrixEntry_add,polarMatrixEntry_one,originalSignedCofactorRow]

end Grad.ActualPolarFlux
