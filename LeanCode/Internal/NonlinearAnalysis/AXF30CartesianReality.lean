import AXF29CartesianConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

open scoped ComplexConjugate

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection
open Grad.CompletedReality

variable {parameters : PhaseParameters}

theorem spinValue_conjugate (sign : ℝ) (value : ComplexEuclidean 2) :
    spinValue (sign : ℂ) (cartesianPhysicalConjugation 2 value) =
      cartesianPhysicalConjugation 1 (spinValue (-(sign : ℂ)) value) := by
  apply PiLp.ext
  intro component
  fin_cases component
  simp [spinValue_apply, cartesianPhysicalConjugation]

theorem spinCore_conjugate (sign : ℝ) (field : ACore parameters 2) :
    spinCore (sign : ℂ) (cartesianCoreConjugation parameters field) =
      cartesianCoreConjugation parameters (spinCore (-(sign : ℂ)) field) := by
  apply Grad.NonlinearQuotientBounds.acore_ext
  intro cell point
  change (valueMapJet (spinValue (sign : ℂ))
    ((cartesianCoreConjugation parameters field).val cell)).value point =
      cartesianPhysicalConjugation 1
        ((valueMapJet (spinValue (-(sign : ℂ))) (field.val (-cell))).value point)
  rw [valueMapJet_value, valueMapJet_value]
  exact spinValue_conjugate sign ((field.val (-cell)).value point)

def cartesianSourceConjugation (source : CartesianSourceCore parameters) : CartesianSourceCore parameters :=
  (cartesianCoreConjugation parameters source.1,
    cartesianCoreConjugation parameters source.2.1,
    cartesianCoreConjugation parameters source.2.2)

/-- BS2 preserves the actual real Fourier condition, including cell reversal
and the spin swap. It is not componentwise conjugation of spin coordinates. -/
theorem spinCartesianEquiv_conjugation (source : SmoothQuotient parameters) :
    spinCartesianEquiv (zCoreConjugation parameters source) =
      cartesianSourceConjugation (spinCartesianEquiv source) := by
  apply Prod.ext
  · change cartesianSourceVector (zCoreConjugation parameters source) =
      cartesianCoreConjugation parameters (cartesianSourceVector source)
    apply spinCore_joint_injective
    · rw [spinCore_cartesianSource_plus]
      have law := spinCore_conjugate (parameters := parameters) 1 (cartesianSourceVector source)
      norm_num only [Complex.ofReal_one] at law
      rw [law, spinCore_cartesianSource_minus]
      rfl
    · rw [spinCore_cartesianSource_minus]
      have law := spinCore_conjugate (parameters := parameters) (-1) (cartesianSourceVector source)
      norm_num only [Complex.ofReal_neg, Complex.ofReal_one, neg_neg] at law
      rw [law, spinCore_cartesianSource_plus]
      rfl
  · rfl

theorem spinCartesianEquiv_real_iff (source : SmoothQuotient parameters) :
    zCoreConjugation parameters source = source ↔
      cartesianSourceConjugation (spinCartesianEquiv source) = spinCartesianEquiv source := by
  rw [← spinCartesianEquiv_conjugation]
  exact spinCartesianEquiv.injective.eq_iff.symm

end Grad.FlatSourceProjection
