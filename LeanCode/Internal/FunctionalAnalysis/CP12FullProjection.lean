import CP11VectorProjection
import SM15StateCarrier
import AX8AmbientDensity

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SmoothingFamily Grad.ImplementationReadiness Grad.AxisCore Grad.FourierGrade

/-! # COR18: the smooth full-domain projection `P_M(τ, u, s) = (τ, P_M^u u, (I - Π) s)`

On the accepted smooth product `StateCore` (COR17's carrier): identity on the
free axis coordinate, the ordered N31 vector projection on the three-vector,
and the angular-mean removal on the scalar. Linear, bounded at every grade
`q ≥ 3` in the literal COR17 product norm, idempotent, with exact range. -/

variable (parameters : PhaseParameters) (parameter : Seed.Parameters)
  (inside : parameter ∈ Seed.parameterDomain)

/-- The literal N8 full-domain projection on the smooth product. -/
def fullProjection : StateCore parameters →ₗ[ℂ] StateCore parameters :=
  (LinearMap.fst ℂ (AxisCore parameters.sigma0 (ComplexEuclidean 2))
      (ACore parameters 3 × ACore parameters 1)).prod
    (((vectorProjection parameters parameter inside).comp
        ((LinearMap.fst ℂ (ACore parameters 3) (ACore parameters 1)).comp
          (LinearMap.snd ℂ (AxisCore parameters.sigma0 (ComplexEuclidean 2))
            (ACore parameters 3 × ACore parameters 1)))).prod
      ((LinearMap.id - angularCore parameters 0).comp
        ((LinearMap.snd ℂ (ACore parameters 3) (ACore parameters 1)).comp
          (LinearMap.snd ℂ (AxisCore parameters.sigma0 (ComplexEuclidean 2))
            (ACore parameters 3 × ACore parameters 1)))))

theorem fullProjection_apply (state : StateCore parameters) :
    fullProjection parameters parameter inside state =
      (state.1, vectorProjection parameters parameter inside state.2.1,
        state.2.2 - angularCore parameters 0 state.2.2) := by
  unfold fullProjection
  simp only [LinearMap.prod_apply, Function.prod, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.sub_apply, LinearMap.id_apply]

/-- The full constraint kernel: free axis coordinate, the vector constraints,
and a mean-zero scalar. -/
def FullConstraints (state : StateCore parameters) : Prop :=
  VectorConstraints parameters parameter inside state.2.1 ∧
    angularCore parameters 0 state.2.2 = 0

theorem angularCore_zero_sub_self (scalar : ACore parameters 1) :
    angularCore parameters 0 (scalar - angularCore parameters 0 scalar) = 0 := by
  rw [map_sub, angularCore_projection, if_pos rfl, sub_self]

theorem fullProjection_constraints (state : StateCore parameters) :
    FullConstraints parameters parameter inside (fullProjection parameters parameter inside state) := by
  rw [fullProjection_apply]
  exact ⟨vectorProjection_constraints parameters parameter inside state.2.1,
    angularCore_zero_sub_self parameters state.2.2⟩

theorem fullProjection_fixes (state : StateCore parameters)
    (constraints : FullConstraints parameters parameter inside state) :
    fullProjection parameters parameter inside state = state := by
  obtain ⟨vector, scalar⟩ := constraints
  rw [fullProjection_apply, vectorProjection_fixes parameters parameter inside _ vector, scalar,
    sub_zero]

theorem fullProjection_idempotent (state : StateCore parameters) :
    fullProjection parameters parameter inside (fullProjection parameters parameter inside state) =
      fullProjection parameters parameter inside state :=
  fullProjection_fixes parameters parameter inside _
    (fullProjection_constraints parameters parameter inside state)

theorem fullProjection_range_iff (state : StateCore parameters) :
    (∃ source : StateCore parameters, fullProjection parameters parameter inside source = state) ↔
      FullConstraints parameters parameter inside state := by
  constructor
  · rintro ⟨source, rfl⟩
    exact fullProjection_constraints parameters parameter inside source
  · intro constraints
    exact ⟨state, fullProjection_fixes parameters parameter inside state constraints⟩

/-- The scalar mean removal is bounded at every grade. -/
theorem meanRemoval_norm_le (grade : ℕ) (scalar : ACore parameters 1) :
    ‖GradeCore.ofCoreLinear (grade := grade) (scalar - angularCore parameters 0 scalar)‖ ≤
      (1 + |orthogonalGradeConstant grade|) * ‖GradeCore.ofCoreLinear (grade := grade) scalar‖ := by
  rw [map_sub, ofCoreLinear_norm_coordinates]
  calc ‖GradeCore.ofCoreLinear (grade := grade) scalar -
        GradeCore.ofCoreLinear (grade := grade) (angularCore parameters 0 scalar)‖
      ≤ ‖GradeCore.ofCoreLinear (grade := grade) scalar‖ +
          ‖GradeCore.ofCoreLinear (grade := grade) (angularCore parameters 0 scalar)‖ :=
        norm_sub_le _ _
    _ ≤ ‖cartesianGradeCoordinates parameters grade scalar‖ +
          |orthogonalGradeConstant grade| * ‖cartesianGradeCoordinates parameters grade scalar‖ := by
        rw [ofCoreLinear_norm_coordinates, ofCoreLinear_norm_coordinates]
        exact add_le_add le_rfl ((angularCore_coordinates_bound parameters 0 scalar grade).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
    _ = (1 + |orthogonalGradeConstant grade|) * ‖cartesianGradeCoordinates parameters grade scalar‖ := by
        ring

/-- The same-grade bound in the literal COR17 product norm for every `q ≥ 3`. -/
theorem fullProjection_norm_le (grade : ℕ) (gradeLarge : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : StateCore parameters,
      ‖stateToGrade parameters grade (fullProjection parameters parameter inside state)‖ ≤
        constant * ‖stateToGrade parameters grade state‖ := by
  obtain ⟨vectorC, vectorC_nonneg, vectorBound⟩ :=
    vectorProjection_norm_le parameters parameter inside grade gradeLarge
  refine ⟨1 + vectorC + (1 + |orthogonalGradeConstant grade|), by positivity, ?_⟩
  intro state
  rw [fullProjection_apply, stateToGrade_embedded_norm, stateToGrade_embedded_norm]
  dsimp only
  simp only [aGradeEta_norm]
  have axisNorm := norm_nonneg (axisToGrade parameters.sigma0 (grade + 1) state.1)
  have vectorNorm := norm_nonneg (GradeCore.ofCoreLinear (grade := grade) state.2.1)
  have scalarNorm := norm_nonneg (GradeCore.ofCoreLinear (grade := grade) state.2.2)
  have vector := vectorBound state.2.1
  have scalar := meanRemoval_norm_le parameters grade state.2.2
  have absNonneg := abs_nonneg (orthogonalGradeConstant grade)
  nlinarith [mul_nonneg vectorC_nonneg axisNorm, mul_nonneg vectorC_nonneg scalarNorm,
    mul_nonneg absNonneg axisNorm, mul_nonneg absNonneg vectorNorm]

end Grad.Cor18
