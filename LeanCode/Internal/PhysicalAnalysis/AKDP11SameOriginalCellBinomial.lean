import AKDP10SameOriginalPlanarGraphNorm
import AKDM3OriginalPureCellNorm
import CB1Proof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.NonlinearProduct Grad.OriginalCartesianTameEstimate
open Grad.CellWeights Grad.CellBinomial

/-- All natural moments of the literal original weighted core. -/
def startupOriginalAllMoments {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) : StartupAllMoments dimension where
  field := originalSourceJointField parameters core 0
  moment := originalSourceJointField parameters core
  zero := rfl
  same := by
    have grades := ae_all_iff.mpr (originalSourceJointField_same parameters core)
    filter_upwards [grades,originalSourceJointField_same parameters core 0] with point all zero
    intro grade cell
    simp only [pow_zero,one_smul] at zero
    simpa only [cellFrequency] using
      (all grade cell).trans (congrArg (cellWeight cell^grade • ·) (zero cell).symm)

theorem startupOriginalAllMoments_projection {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell (startupOriginalAllMoments parameters core).field =
      closedDerivativeL2 (0,0) (phaseWeightedJet parameters cell (core.val cell)) := by
  rw [show (startupOriginalAllMoments parameters core).field = originalSourceJointField parameters core 0 from rfl,
    startupOriginalJoint_projection,originalSourceCellCoordinate_value]
  simp only [pow_zero,one_smul]
  change closedContinuousToDiskL2 _ = closedContinuousToDiskL2 _
  rw [closedMultiDerivative_zero]

/-- Exact binomial expression for the original pure-cell norm in the
SAME signed moments. The fixed ell/L normalization is explicit. -/
theorem startupOriginalCellNorm_binomial {dimension : ℕ} (parameters : PhaseParameters) {L ell : ℝ}
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (core : ACore parameters dimension) (family : StartupSignedFamily dimension L ell)
    (same : family.field = (originalSourceMoments parameters core).field) (grade : ℕ) :
    originalCellNorm parameters grade core^2 =
      ∑ power : Fin (grade+1),(grade.choose power.val : ℝ)*
        ‖(((((ell/L : ℝ) : ℂ)⁻¹)^power.val) • family.moment power.val)‖^2 := by
  let moments := startupOriginalAllMoments parameters core
  have natural : (family.field,moments.moment grade) ∈ fieldGraph dimension openUnitDisk (positiveFactor grade) := by
    apply (fieldGraph_mem dimension openUnitDisk _ _ _).mpr
    intro cell
    rw [same]
    change fieldCellProjection dimension openUnitDisk cell (originalSourceJointField parameters core grade) =
      positiveFactor grade cell • fieldCellProjection dimension openUnitDisk cell (originalSourceJointField parameters core 0)
    rw [startupOriginalJoint_projection,startupOriginalJoint_projection,originalSourceCellCoordinate_value,
      originalSourceCellCoordinate_value]
    simp only [pow_zero,one_smul,positiveFactor,cellWeight,cellFrequency]
  have signed (power : Fin (grade+1)) :
      (family.field,(((((ell/L : ℝ) : ℂ)⁻¹)^power.val) • family.moment power.val)) ∈
        fieldGraph dimension openUnitDisk (derivativeFactor power.val) :=
    (fieldGraph_mem dimension openUnitDisk _ _ _).mpr (family.unscaledProjection lengthNonzero scaleNonzero power.val)
  have equation := field_binomial dimension grade openUnitDisk family.field (moments.moment grade)
    (fun power : Fin (grade+1) => (((((ell/L : ℝ) : ℂ)⁻¹)^power.val) • family.moment power.val)) natural signed
  rw [← originalCellNorm_eq_actualMoment parameters core moments
    (startupOriginalAllMoments_projection parameters core) grade] at equation
  exact equation

/-- The binomial norm bound keeps only a finite sum of actual signed
moments; its coefficients are fixed before either state or field. -/
theorem startupOriginalCellNorm_le_signed {dimension : ℕ} (parameters : PhaseParameters) {L ell : ℝ}
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (core : ACore parameters dimension) (family : StartupSignedFamily dimension L ell)
    (same : family.field = (originalSourceMoments parameters core).field) (grade : ℕ) :
    originalCellNorm parameters grade core ≤
      ∑ power : Fin (grade+1),Real.sqrt (grade.choose power.val : ℝ)*
        ‖((((ell/L : ℝ) : ℂ)⁻¹)^power.val)‖*‖family.moment power.val‖ := by
  let values := fun power : Fin (grade+1) =>
    (Real.sqrt (grade.choose power.val : ℝ)) •
      (((((ell/L : ℝ) : ℂ)⁻¹)^power.val) • family.moment power.val)
  have squared : ‖(WithLp.toLp 2 values : PiLp 2 (fun _ : Fin (grade+1) => StartupL2 dimension))‖^2 =
      originalCellNorm parameters grade core^2 := by
    rw [PiLp.norm_sq_eq_of_L2,startupOriginalCellNorm_binomial parameters lengthNonzero scaleNonzero core family same grade]
    apply Finset.sum_congr rfl
    intro power _
    change ‖values power‖^2 = _
    rw [show values power = _ from rfl,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have exactNorm := (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp squared
  change ‖(WithLp.toLp 2 values : PiLp 2 (fun _ : Fin (grade+1) => StartupL2 dimension))‖ = originalCellNorm parameters grade core at exactNorm
  rw [← exactNorm]
  apply (startupFiniteHilbert_norm_le_sum values).trans_eq
  apply Finset.sum_congr rfl
  intro power _
  simp only [values,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

end Grad.CartesianStartup
