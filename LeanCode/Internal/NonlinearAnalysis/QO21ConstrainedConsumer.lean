import QO20FixedSliceRange

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.CompletedReality Grad.RealFixedRanges Grad.AxisCore Grad.QuotientProjection
open Grad.SmoothingFamily

/-- Coefficient-identical passage between the two existing all-grade axis
cores. The weighted square terms, and hence the analytic width, are unchanged. -/
def axisToTangent (parameters : PhaseParameters) :
    Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2) →ₗ[ℂ]
      TangentCoefficient parameters where
  toFun family := ⟨family.val, fun grade => by
    have summable := (memlp_iff_summable_sq _).mp (family.property grade)
    apply summable.congr
    intro cell
    change ‖(Grad.AxisCore.axisWeight parameters grade cell : ℂ) • family.val cell‖ ^ 2 = _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (axisWeight_pos parameters grade cell), mul_pow]
    unfold Grad.AxisCore.axisWeight tangentNormTerm
    simp only [mul_pow, ← pow_mul, Nat.mul_comm grade 2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem axisToTangent_coefficients (parameters : PhaseParameters)
    (family : Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2)) :
    (axisToTangent parameters family).val = family.val := rfl

def stateChart (parameters : PhaseParameters) (state : StateCore parameters) :
    ChartState parameters := (axisToTangent parameters state.1, state.2)

theorem stateChart_real (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR) :
    RealTangent (stateChart parameters state.val).1 ∧
    cartesianCoreConjugation parameters state.val.2.1 = state.val.2.1 ∧
    cartesianCoreConjugation parameters state.val.2.2 = state.val.2.2 := by
  have real := ((mem_stateSmoothRange parameters reference insideR state.val).1 state.property).2
  refine ⟨?_, congrArg (fun field : StateCore parameters => field.2.1) real,
    congrArg (fun field : StateCore parameters => field.2.2) real⟩
  intro cell index
  have coefficient := congrArg (fun field : StateCore parameters => field.1.val (-cell) index) real
  change (starRingEnd ℂ) (state.val.1.val (-(-cell)) index) = state.val.1.val (-cell) index at coefficient
  change state.val.1.val (-cell) index = (starRingEnd ℂ) (state.val.1.val cell index)
  simpa only [neg_neg] using coefficient.symm

/-- Actual O21 consumer: a real curvature and a member of the canonical
reference constraint carrier, restricted only by the original Q13 axis
condition, map to the original real compatible quotient carrier. -/
theorem fixedSliceMap_constrained_mem (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (axis : ChartAxisCondition (stateChart parameters state.val)) :
    fixedSliceMap parameters cellLength reference insideR seed insideS
      ((epsilon : ℂ), stateChart parameters state.val) ∈ sourceSmoothRange parameters := by
  have constraints := Grad.ConstrainedTransfer.smoothState_constraints parameters reference insideR state
  obtain ⟨real, vectorReal, scalarReal⟩ := stateChart_real parameters reference insideR state
  exact fixedSliceMap_mem cellLength epsilon reference insideR seed insideS _
    constraints.1.1 real axis vectorReal scalarReal constraints.2

/-- Immediate consumer in every original admissible quotient Banach grade;
the map is embedded unchanged, without inserting a target projection. -/
theorem fixedSliceMap_constrained_grade_mem (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade)
    (state : stateSmoothRange parameters reference insideR)
    (axis : ChartAxisCondition (stateChart parameters state.val)) :
    quotientEta parameters grade (fixedSliceMap parameters cellLength reference insideR seed insideS
      ((epsilon : ℂ), stateChart parameters state.val)) ∈ sourceRange parameters grade large :=
  (quotientEta_mem_iff parameters grade large _).2
    (fixedSliceMap_constrained_mem parameters cellLength epsilon reference insideR seed insideS state axis)

end Grad.NonlinearRange
