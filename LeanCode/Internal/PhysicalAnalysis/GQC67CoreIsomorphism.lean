import GQC66PhysicalCoreConsumer

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.GaugeTransfer

/-- The actual AO20–22 smooth core isomorphism. Its domain is the
corrected compensated core and its target is the actual current gauged
flat core, with both original graph estimates and the literal maps. -/
structure SmoothCompensatedCoreIsomorphism {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) where
  coherent : FamilyCoherent gauge
  inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)
  equivalence : circularCompensatedCore admissible ≃ₗ[ℂ] currentCompensatedCore admissible gauge coherent
  forward : ∀ data, (equivalence data).val = compensatedForward admissible gauge coherent inverseCoherent data.val
  backward : ∀ data, (equivalence.symm data).val = compensatedBackward L sigma gamma ell data.val
  forwardReconstruction : ∀ data, compensatedReconstruct admissible (equivalence data).val =
    apSmoothCurrent admissible gauge coherent inverseCoherent (compensatedReconstruct admissible data.val)
  backwardReconstruction : ∀ data, compensatedReconstruct admissible (equivalence.symm data).val =
    apSmoothCircle L sigma gamma ell (compensatedReconstruct admissible data.val)
  differenceBound : ∀ grade, 3 ≤ grade → ∀ data,
    compensatedNorm admissible grade ((equivalence data).val - data.val) ≤
      (transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) * compensatedNorm admissible grade data.val
  forwardBound : ∀ grade, 3 ≤ grade → ∀ data,
    compensatedNorm admissible grade (equivalence data).val ≤
      ((transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3))) + 1) * compensatedNorm admissible grade data.val
  backwardBound : ∀ grade, ∀ data,
    compensatedNorm admissible grade (equivalence.symm data).val ≤
      (backwardDifferenceConstant grade + 1) * compensatedNorm admissible grade data.val

def smoothCompensatedCoreIsomorphism {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)
    (small : ‖determinantInverseInput admissible gauge 0‖ ≤ 1 / 2) :
    SmoothCompensatedCoreIsomorphism admissible gauge where
  coherent := coherent
  inverseCoherent := inverseCoherent
  equivalence := compensatedCoreEquivalence admissible gauge coherent inverseCoherent laws
  forward _ := rfl
  backward _ := rfl
  forwardReconstruction data := compensatedForward_reconstruct admissible gauge coherent inverseCoherent data.val
  backwardReconstruction data := compensatedBackward_reconstruct admissible data.val
    ((mem_compensatedFlatCore admissible data.val).mp data.property.1).1.1
  differenceBound := compensatedForward_polynomial_difference admissible gauge coherent inverseCoherent laws small
  forwardBound := compensatedCoreEquivalence_norm_bound admissible gauge coherent inverseCoherent laws small
  backwardBound := compensatedCoreEquivalence_inverse_norm_bound admissible gauge coherent inverseCoherent laws

theorem SmoothCompensatedCoreIsomorphism.left_inverse {L sigma gamma ell : ℝ}
    {admissible : Admissible L sigma gamma ell} {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge) (data : circularCompensatedCore admissible) :
    isomorphism.equivalence.symm (isomorphism.equivalence data) = data := isomorphism.equivalence.symm_apply_apply data

theorem SmoothCompensatedCoreIsomorphism.right_inverse {L sigma gamma ell : ℝ}
    {admissible : Admissible L sigma gamma ell} {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge) (data : currentCompensatedCore admissible gauge isomorphism.coherent) :
    isomorphism.equivalence (isomorphism.equivalence.symm data) = data := isomorphism.equivalence.apply_symm_apply data

end Grad.GaugeCoefficients.Physical.Compensated
