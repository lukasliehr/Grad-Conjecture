import AKCO5ExactSignedCellFamilies
import CB1Consumers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.CellWeights Grad.CellBinomial

private def signedZeroGraph {dimension : ℕ} (field : StartupL2 dimension) : GraphGrade dimension 0 0 openUnitDisk :=
  ofCoordinates dimension 0 openUnitDisk (fun _ => 0) (fun _ => field) (by
    intro index cell vector test
    have same : index = zeroIndex 0 := by
      apply Subtype.ext
      change index.val = (0,0)
      have bound := index.property
      exact Prod.ext (by omega) (by omega)
    subst index
    simp only [degree_zero,inverseFieldCLM_zero,ContinuousLinearMap.id_apply,positiveFactor,pow_zero,one_mul]
    rfl)

private theorem signedZeroGraph_base {dimension : ℕ} (field : StartupL2 dimension) :
    base dimension 0 openUnitDisk (fun _ => 0) (signedZeroGraph field) = field := by
  rw [base_apply,inverseFieldCLM_zero]
  rfl

private theorem signedFrequency_factor (L ell : ℝ) (cell : ℤ) :
    startupAxialFrequency L ell cell = ((ell/L : ℝ) : ℂ) * (Complex.I*(cell : ℂ)) := by
  unfold startupAxialFrequency
  push_cast
  ring

/-- Remove only the fixed nonzero scale factor to feed the accepted
CellBinomial synthesis with its literal (I*n)^p derivative convention. -/
theorem StartupSignedFamily.unscaledProjection {dimension : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (power : ℕ) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell
      (((((ell/L : ℝ) : ℂ)⁻¹)^power) • family.moment power) =
        derivativeFactor power cell • fieldCellProjection dimension openUnitDisk cell family.field := by
  rw [map_smul,family.projection,smul_smul,signedFrequency_factor,mul_pow,← mul_assoc]
  have nonzero : ((ell/L : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (div_ne_zero scaleNonzero lengthNonzero)
  simp only [inv_pow,inv_mul_cancel₀ (pow_ne_zero power nonzero),one_mul,derivativeFactor]

def StartupSignedFamily.derivativeZeroJet {dimension : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (power : ℕ) : DerivativeJet dimension 0 power openUnitDisk family.field :=
  operatorJetOfGraph dimension 0 openUnitDisk (derivativeFactor power) family.field
    (signedZeroGraph (((((ell/L : ℝ) : ℂ)⁻¹)^power) • family.moment power)) (by
      rw [signedZeroGraph_base]
      exact (fieldGraph_mem dimension openUnitDisk _ _ _).mpr
        (family.unscaledProjection lengthNonzero scaleNonzero power))

/-- Existing literal CellBinomial all-cell synthesis supplies all natural
weights of the SAME output field. Its theorem and proof remain unchanged. -/
theorem StartupSignedFamily.allNaturalZeroGraphs {dimension : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0) :
    ∀ weight : ℕ, ∃ graph : GraphGrade dimension 0 weight openUnitDisk,
      base dimension 0 openUnitDisk (fun _ => weight) graph = family.field := by
  apply (allCellConsumer dimension 0 openUnitDisk openUnitDisk_isOpen family.field).mpr
  intro power
  let jet := family.derivativeZeroJet lengthNonzero scaleNonzero power
  exact ⟨jet.inDomain,jet.jet,jet.base_eq⟩

end Grad.CartesianStartup
