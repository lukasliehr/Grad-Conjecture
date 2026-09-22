import ANV7ActualCompensatedBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
variable {L sigma gamma ell : ℝ}

theorem apVectorInverse_firstJet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apVectorInverse admissible field) := by
  have signed (sign : ℤ) : APSmoothAxisFirstJetZero admissible (apSignedInverse admissible sign field) :=
    apShiftInverse_firstJet admissible sign _
      (apSmoothValueMap_preserves_firstJet admissible (helicityValue sign) field flat)
  exact (mem_apSmoothAxisFirsts admissible _).mp
    ((apSmoothAxisFirsts admissible 2).add_mem
      ((mem_apSmoothAxisFirsts admissible _).mpr (signed 1))
      ((mem_apSmoothAxisFirsts admissible _).mpr (signed (-1))))

theorem reconstructionLoad_firstJet (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (force : APSmooth L sigma gamma ell 2)
    (gradientFlat : APSmoothAxisFirstJetZero admissible (apSmoothGradient admissible theta))
    (forceFlat : APSmoothAxisFirstJetZero admissible force) :
    APSmoothAxisFirstJetZero admissible (reconstructionLoad admissible theta force) := by
  have turned := apSmoothValueMap_preserves_firstJet admissible quarterValueMap _ gradientFlat
  exact (mem_apSmoothAxisFirsts admissible _).mp
    ((apSmoothAxisFirsts admissible 2).add_mem
      ((apSmoothAxisFirsts admissible 2).smul_mem (2 : ℂ) ((mem_apSmoothAxisFirsts admissible _).mpr turned))
      ((mem_apSmoothAxisFirsts admissible _).mpr forceFlat))

theorem reconstructedVector_firstJet (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (force : APSmooth L sigma gamma ell 2)
    (gradientFlat : APSmoothAxisFirstJetZero admissible (apSmoothGradient admissible theta))
    (forceFlat : APSmoothAxisFirstJetZero admissible force) :
    APSmoothAxisFirstJetZero admissible (reconstructedVector admissible theta force) := by
  have original := apVectorInverse_firstJet admissible _
    (reconstructionLoad_firstJet admissible theta force gradientFlat forceFlat)
  exact (mem_apSmoothAxisFirsts admissible _).mp
    ((apSmoothAxisFirsts admissible 2).neg_mem ((mem_apSmoothAxisFirsts admissible _).mpr original))

theorem storedPair_firstJet (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (scalar : APSmooth L sigma gamma ell 1)
    (vectorFlat : APSmoothAxisFirstJetZero admissible vector) (scalarFlat : APSmoothAxisFirstJetZero admissible scalar) :
    APSmoothAxisFirstJetZero admissible (storedPair L sigma gamma ell vector scalar) :=
  (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible 3).add_mem
    ((mem_apSmoothAxisFirsts admissible _).mpr (apSmoothValueMap_preserves_firstJet admissible planarInclusionMap vector vectorFlat))
    ((mem_apSmoothAxisFirsts admissible _).mpr (apSmoothValueMap_preserves_firstJet admissible toroidalInclusionMap scalar scalarFlat)))

theorem reconstructedState_stored_firstJet (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (gradientFlat : APSmoothAxisFirstJetZero admissible (apSmoothGradient admissible theta))
    (forceFlat : APSmoothAxisFirstJetZero admissible source.1) :
    APSmoothAxisFirstJetZero admissible (reconstructedState admissible theta source).2 :=
  storedPair_firstJet admissible _ _ (reconstructedVector_firstJet admissible theta source.1 gradientFlat forceFlat)
    (apShiftInverse_firstJet admissible 0 source.2.2
      (Grad.ActualMeanInverse.actualSource_conditions admissible source compatible).2.2.2)

end Grad.ActualNonexceptionalInverse
