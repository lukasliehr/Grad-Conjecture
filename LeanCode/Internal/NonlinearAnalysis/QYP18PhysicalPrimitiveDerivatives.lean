import QYP17PhysicalFixedDerivatives
import QY34MultiplierGenuine

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open Filter
open scoped Topology ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.QuotientProjection Grad.MixedQuotientComposition

theorem completedPolynomial_derivative_core (parameters : PhaseParameters) (cellLength : ℝ)
    (grade order : ℕ) (base : QuotientState parameters) (directions : Fin order → QuotientState parameters) :
    iteratedFDeriv ℝ order (completedPolynomial parameters cellLength grade)
      (polynomialStateEmbed parameters (grade + 6) base)
      (fun position => polynomialStateEmbed parameters (grade + 6) (directions position)) =
    quotientEta parameters grade
      (quotientRowsDerivative parameters cellLength order base (fun position => directions position.rev)) := by
  apply iteratedFDeriv_core_of_directional
    ((polynomialStateEmbed parameters (grade + 6)).restrictScalars ℝ)
    (completedPolynomial parameters cellLength grade) Set.univ isOpen_univ
    (completedPolynomial_contDiff parameters cellLength grade).contDiffOn
    (fun count point tuple => quotientEta parameters grade
      (quotientRowsDerivative parameters cellLength count point tuple))
  · intro point _ tuple
    rw [quotientRowsDerivative_zeroth]
    exact (completedPolynomial_core parameters cellLength grade point).symm
  · intro count point tuple _
    apply rows_hasDerivAt_of_directional parameters grade
      (fun state => quotientRowsDerivative parameters cellLength count state (fun position => tuple position.castSucc))
      point (tuple (Fin.last count)) (quotientRowsDerivative parameters cellLength (count + 1) point tuple)
    intro q
    have genuine := quotientRowsDerivative_genuine cellLength count point tuple q
    have scalar (t : ℝ) (value : QuotientState parameters) : (t : ℂ) • value = t • value :=
      Complex.coe_smul t value
    have rowsScalar (t : ℝ) (value : QuotientRows parameters) : (t : ℂ) • value = t • value :=
      Complex.coe_smul t value
    simpa only [← Complex.ofReal_inv, scalar, rowsScalar] using genuine
  · exact Set.mem_univ base

def completedPhysicalReferenceState (parameters : PhaseParameters) (reference : Seed.Parameters)
    (seed : Seed.Parameters) (grade : ℕ) (state : JointAmbient parameters grade) :
    PolynomialState parameters grade :=
  completedPhysicalMixedReferenceState parameters reference grade (jointAtSeed parameters grade seed state)

theorem completedPhysicalReferenceState_contDiffOn (parameters : PhaseParameters) (reference : Seed.Parameters)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedPhysicalReferenceState parameters reference seed grade) (jointDomain parameters grade) :=
  (completedPhysicalMixedReferenceState_contDiffOn parameters reference grade).comp
    (jointAtSeed_contDiff parameters grade seed).contDiffOn (fun _ member => ⟨insideS, member⟩)

theorem completedPhysicalReferenceState_core (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base : JointState parameters) (axis : ChartAxisCondition base.2) :
    completedPhysicalReferenceState parameters reference seed grade (jointCoreEmbed parameters grade base) =
    polynomialStateEmbed parameters grade (physicalReferenceState parameters reference insideR seed insideS base) :=
  completedPhysicalMixedReferenceState_core parameters reference insideR grade (seed, base) insideS axis

theorem completedPhysicalReferenceState_derivative_core (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : JointState parameters) (axis : ChartAxisCondition base.2)
    (directions : Fin order → JointState parameters) :
    iteratedFDeriv ℝ order (completedPhysicalReferenceState parameters reference seed grade)
      (jointCoreEmbed parameters grade base) (fun position => jointCoreEmbed parameters grade (directions position)) =
    polynomialStateEmbed parameters grade
      (physicalFixedReferenceFamily parameters reference insideR seed insideS order base (fun position => directions position.rev)) := by
  apply iteratedFDeriv_core_of_directional ((jointCoreLinear parameters grade).restrictScalars ℝ)
    (completedPhysicalReferenceState parameters reference seed grade) (jointDomain parameters grade)
    (jointDomain_isOpen parameters grade)
    (completedPhysicalReferenceState_contDiffOn parameters reference seed insideS grade)
    (fun count point tuple => polynomialStateEmbed parameters grade
      (physicalFixedReferenceFamily parameters reference insideR seed insideS count point tuple))
  · intro point member tuple
    rw [physicalFixedReferenceFamily_zero]
    exact (completedPhysicalReferenceState_core parameters reference insideR seed insideS grade point
      ((jointDomain_core_iff parameters grade point).1 member)).symm
  · intro count point tuple member
    apply (coreCurve_hasDerivAt_iff (polynomialStateEmbed parameters grade) (stateNorm grade)
      (polynomialStateEmbed_norm parameters grade) _ _).2
    have genuine := physicalFixedReferenceFamily_genuine reference insideR seed insideS count point tuple
      ((jointDomain_core_iff parameters grade point).1 member) grade
    have scalar (t : ℝ) (value : JointState parameters) : (t : ℂ) • value = t • value :=
      Complex.coe_smul t value
    simpa only [zero_smul ℝ (tuple (Fin.last count)), add_zero, scalar] using genuine
  · exact (jointDomain_core_iff parameters grade base).2 axis

/-- Exact first chain rule with the literal quotient derivative and the
physical chart derivative, independent of all mixed seed calculations. -/
theorem completedPhysicalFixedSlice_first_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (base direction : JointState parameters) (axis : ChartAxisCondition base.2) :
    fderiv ℝ (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
      (jointCoreEmbed parameters (grade + 6) base) (jointCoreEmbed parameters (grade + 6) direction) =
    quotientEta parameters grade (quotientRowsDerivative parameters cellLength 1
      (physicalReferenceState parameters reference insideR seed insideS base)
      (fun _ => physicalFixedReferenceFamily parameters reference insideR seed insideS 1 base (fun _ => direction))) := by
  have inside := (jointDomain_core_iff parameters (grade + 6) base).2 axis
  have innerSmooth := (completedPhysicalReferenceState_contDiffOn parameters reference seed insideS (grade + 6)).contDiffAt
    ((jointDomain_isOpen parameters (grade + 6)).mem_nhds inside)
  have chain := ((completedPolynomial_contDiff parameters cellLength grade).differentiable (by simp)
    (completedPhysicalReferenceState parameters reference seed (grade + 6) (jointCoreEmbed parameters (grade + 6) base))).hasFDerivAt.comp
      (jointCoreEmbed parameters (grade + 6) base) (innerSmooth.differentiableAt (by simp)).hasFDerivAt
  have equality := congrArg (fun mapping => mapping (jointCoreEmbed parameters (grade + 6) direction)) chain.fderiv
  have inner := completedPhysicalReferenceState_derivative_core parameters reference insideR seed insideS
    (grade + 6) 1 base axis (fun _ => direction)
  rw [iteratedFDeriv_one_apply] at inner
  rw [ContinuousLinearMap.comp_apply, inner,
    completedPhysicalReferenceState_core parameters reference insideR seed insideS (grade + 6) base axis] at equality
  have outer := completedPolynomial_derivative_core parameters cellLength grade 1
    (physicalReferenceState parameters reference insideR seed insideS base)
    (fun _ => physicalFixedReferenceFamily parameters reference insideR seed insideS 1 base (fun _ => direction))
  rw [iteratedFDeriv_one_apply] at outer
  exact equality.trans outer

end Grad.PhysicalCoordinates
