import QY15MixedCompositionBound

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open Filter
open scoped Topology ContDiff

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization
open Grad.QuotientProjection

variable {parameters : PhaseParameters}

/-- The literal open-domain core condition, not a compact-patch interior. -/
def CoreAdmissible (base : Input parameters) : Prop :=
  base.1 ∈ Seed.parameterDomain ∧ ChartAxisCondition base.2.2

theorem CoreAdmissible_iff_domain (grade : ℕ) (base : Input parameters) :
    CoreAdmissible base ↔ mixedCoreEmbed parameters grade base ∈ mixedDomain parameters grade :=
  (mixedDomain_core_iff parameters grade base).symm

section ActualIdentification

variable (family : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → QuotientState parameters)
  (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (zeroth : ∀ (base : Input parameters) (insideS : base.1 ∈ Seed.parameterDomain),
    ChartAxisCondition base.2.2 → ∀ directions,
      family 0 base directions = referenceState parameters reference insideR base.1 insideS base.2)
  (genuine : ∀ order base (directions : Fin (order + 1) → Input parameters),
    CoreAdmissible base → IsStateDirectionalDerivative
      (fun point => family order point (fun position => directions position.castSucc))
      base (directions (Fin.last order)) (family (order + 1) base directions))

include zeroth genuine in
/-- A genuine literal inner tower gives the actual completed mixed
Fréchet derivative, through the unchanged five homogeneous quotient parts. -/
theorem mixedComposedDerivative_core (cellLength : ℝ) (grade order : ℕ)
    (base : Input parameters) (admissible : CoreAdmissible base)
    (directions : Fin order → Input parameters) :
    iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade)
      (mixedCoreEmbed parameters (grade + 6) base)
      (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade
        (composedDerivative family cellLength order base (fun position => directions position.rev)) := by
  apply mixed_iteratedFDeriv_of_directional parameters cellLength reference grade
    (composedDerivative family cellLength)
  · intro point member tuple
    have actual := (CoreAdmissible_iff_domain (grade + 6) point).2 member
    rw [completedMixedSlice_core parameters cellLength reference insideR grade point actual.1 actual.2,
      composedDerivative_zeroth, zeroth point actual.1 actual.2]
    rfl
  · intro count point tuple member q
    have actual := (CoreAdmissible_iff_domain (grade + 6) point).2 member
    have step := composedDerivative_genuine family CoreAdmissible genuine cellLength count point tuple actual q
    have scalar (t : ℝ) (value : QuotientRows parameters) :
        ((t : ℂ)⁻¹) • value = t⁻¹ • value := by
      rw [← Complex.ofReal_inv, Complex.coe_smul (t⁻¹) value]
    simpa only [scalar] using step
  · exact (CoreAdmissible_iff_domain (grade + 6) base).1 admissible

end ActualIdentification

end Grad.MixedQuotientComposition
