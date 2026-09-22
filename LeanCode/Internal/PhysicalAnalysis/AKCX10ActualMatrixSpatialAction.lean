import AKCX9ActualSpatialComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSpatialAction

/-- The certificate for the actual full coefficient matrix combines its
same-power spatial allocation with full signed output grade preservation. -/
def matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (rank : ℕ)
    (coefficients : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent coefficients)
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0) : StartupSpatialAction rank input output L ell where
  signed := StartupSignedAction.matrix admissible coefficients coherent
  ranked := StartupRankOperator.matrix admissible rank coefficients coherent
  preserves _ _ regular := regular.matrix admissible coefficients coherent lengthNonzero scaleNonzero
  leading family regular field fieldSame image imageSame := by
    obtain ⟨weighted,weightedSame⟩ := regular 0 rank
    rw [family.zero] at weightedSame
    have actualImage : base output rank openUnitDisk (fun _ => 0) image =
        originalMatrixKernel admissible coefficients coherent
          (base input rank openUnitDisk (fun _ => rank) weighted) := by
      rw [weightedSame]
      exact imageSame
    obtain ⟨remainder,same⟩ := startupActualMatrix_rankLeadingFirst admissible coefficients coherent
      (le_refl rank) (le_refl rank) weighted image (le_refl rank) actualImage
    have derivativeSame := startupOrderedDerivative_sameBase weighted (le_refl rank) field (le_refl rank)
      (weightedSame.trans fieldSame.symm)
    rw [derivativeSame] at same
    exact ⟨remainder,same⟩

end StartupSpatialAction
end Grad.CartesianStartup
