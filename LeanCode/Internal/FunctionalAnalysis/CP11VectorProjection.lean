import CP10RowBounds

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.BoundaryTrace Grad.BoundaryLift

/-! # N31: the ordered vector projection `P_M^u = (I - C_{∂,M} B_M)(I - C_t)(I - C_p) Q_A`

Each factor preserves the constraints enforced before it: the gauge
corrections preserve zero first jets (accepted), the outer correction
preserves zero first jets (its collar correction vanishes near the axis) and
both gauges (interior-mode annihilation) and enforces the physical row (N30);
conversely a field in the joint kernel is fixed by every factor. -/

variable (parameters : PhaseParameters) (parameter : Seed.Parameters)
  (inside : parameter ∈ Seed.parameterDomain)

/-- The two zero-first-jet vocabularies agree cell by cell. -/
theorem zeroCartesianFirstJets_iff {dimension : ℕ} (jet : ClosedJet dimension) :
    ZeroCartesianFirstJets jet ↔
      (originValue jet = 0 ∧ ∀ direction : Fin 2, originPartial direction jet = 0) := by
  constructor
  · intro zero
    refine ⟨?_, fun direction => ?_⟩
    · have value := zero 0 (by norm_num) emptyCartesianWord
      rw [closedDerivative_zero_order] at value
      exact value
    · rw [originPartial_eq_closedDerivative]
      exact zero 1 le_rfl (fun _ => direction)
  · rintro ⟨value, partials⟩ order orderLe word
    obtain rfl | rfl : order = 0 ∨ order = 1 := by omega
    · rw [Subsingleton.elim word emptyCartesianWord, closedDerivative_zero_order]
      exact value
    · have wordEq : word = fun _ => word 0 := funext fun index => by rw [Fin.eq_zero index]
      rw [wordEq]
      show closedDerivative jet 1 (fun _ => word 0) originPoint = 0
      rw [← originPartial_eq_closedDerivative]
      exact partials (word 0)

theorem zeroCartesianFirstJets_sub {dimension : ℕ} {first second : ClosedJet dimension}
    (one : ZeroCartesianFirstJets first) (two : ZeroCartesianFirstJets second) :
    ZeroCartesianFirstJets (first - second) := by
  rw [zeroCartesianFirstJets_iff] at one two ⊢
  refine ⟨?_, fun direction => ?_⟩
  · rw [sub_eq_add_neg, originValue_add, originValue_neg, one.1, two.1, neg_zero, add_zero]
  · rw [originPartial_sub, one.2 direction, two.2 direction, sub_zero]

/-- The ordered N31 vector projection. -/
def vectorProjection : ACore parameters 3 →ₗ[ℂ] ACore parameters 3 :=
  (outerCorrection parameters parameter inside).comp
    ((triangularGaugeProjection parameters parameter inside).comp axisJetProjection)

theorem vectorProjection_apply (state : ACore parameters 3) :
    vectorProjection parameters parameter inside state =
      outerCorrection parameters parameter inside
        (triangularGaugeProjection parameters parameter inside (axisJetProjection state)) := rfl

/-- The joint kernel of the vector constraints: zero first jet, both N
gauges, and the N29 physical outer slice. -/
def VectorConstraints (state : ACore parameters 3) : Prop :=
  (∀ cell : ℤ, ZeroCartesianFirstJets (state.1 cell)) ∧
  poloidalCorrection parameters parameter inside state = 0 ∧
  toroidalCorrection parameters parameter inside state = 0 ∧
  physicalRow parameters parameter inside state = 0

/-- Every output of the vector projection lies in the joint kernel. -/
theorem vectorProjection_constraints (state : ACore parameters 3) :
    VectorConstraints parameters parameter inside
      (vectorProjection parameters parameter inside state) := by
  have jetsV : ∀ cell : ℤ, ZeroCartesianFirstJets ((axisJetProjection state).1 cell) := by
    intro cell
    rw [zeroCartesianFirstJets_iff]
    obtain ⟨valueZero, partialZero, _⟩ := consumed_projection_gate state
    exact ⟨valueZero cell, fun direction => partialZero direction cell⟩
  have jetsW : ∀ cell : ℤ, ZeroCartesianFirstJets
      ((triangularGaugeProjection parameters parameter inside (axisJetProjection state)).1 cell) :=
    triangularGaugeProjection_zero_first_jets parameters parameter inside _ jetsV
  have poloidalW : poloidalCorrection parameters parameter inside
      (triangularGaugeProjection parameters parameter inside (axisJetProjection state)) = 0 :=
    triangularProjection_kills_poloidal _ _
      (poloidalCorrection_idempotent parameters parameter inside)
      (poloidal_toroidal_cross parameters parameter inside) _
  have toroidalW : toroidalCorrection parameters parameter inside
      (triangularGaugeProjection parameters parameter inside (axisJetProjection state)) = 0 :=
    triangularProjection_kills_toroidal _ _
      (toroidalCorrection_idempotent parameters parameter inside) _
  rw [vectorProjection_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cell
    rw [outerCorrection_apply]
    show ZeroCartesianFirstJets
      ((triangularGaugeProjection parameters parameter inside (axisJetProjection state)).1 cell -
        (collarCorrection parameters parameter inside (physicalRow parameters parameter inside
          (triangularGaugeProjection parameters parameter inside (axisJetProjection state)))).1 cell)
    exact zeroCartesianFirstJets_sub (jetsW cell)
      (collarCorrection_zeroCartesianFirstJets parameters parameter inside _ cell)
  · exact poloidalCorrection_outerCorrection parameters parameter inside _ poloidalW
  · exact toroidalCorrection_outerCorrection parameters parameter inside _ toroidalW
  · exact physicalRow_outerCorrection parameters parameter inside _

/-- Every field in the joint kernel is fixed by every factor in turn. -/
theorem vectorProjection_fixes (state : ACore parameters 3)
    (constraints : VectorConstraints parameters parameter inside state) :
    vectorProjection parameters parameter inside state = state := by
  obtain ⟨jets, poloidalZero, toroidalZero, rowZero⟩ := constraints
  have axisFixed : axisJetProjection state = state :=
    consumed_projection_fixes state
      (fun cell => ((zeroCartesianFirstJets_iff _).mp (jets cell)).1)
      (fun direction cell => ((zeroCartesianFirstJets_iff _).mp (jets cell)).2 direction)
  have gaugeFixed : triangularGaugeProjection parameters parameter inside state = state :=
    triangularProjection_fixes_kernel _ _ state poloidalZero toroidalZero
  rw [vectorProjection_apply, axisFixed, gaugeFixed]
  exact outerCorrection_fixes parameters parameter inside state rowZero

theorem vectorProjection_idempotent (state : ACore parameters 3) :
    vectorProjection parameters parameter inside
        (vectorProjection parameters parameter inside state) =
      vectorProjection parameters parameter inside state :=
  vectorProjection_fixes parameters parameter inside _
    (vectorProjection_constraints parameters parameter inside state)

/-- The exact range: the joint kernel of the vector constraints. -/
theorem vectorProjection_range_iff (state : ACore parameters 3) :
    (∃ source : ACore parameters 3, vectorProjection parameters parameter inside source = state) ↔
      VectorConstraints parameters parameter inside state := by
  constructor
  · rintro ⟨source, rfl⟩
    exact vectorProjection_constraints parameters parameter inside source
  · intro constraints
    exact ⟨state, vectorProjection_fixes parameters parameter inside state constraints⟩

/-- The same-grade bound of the vector projection for every `q ≥ 3`. -/
theorem vectorProjection_norm_le (grade : ℕ) (gradeLarge : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : ACore parameters 3,
      ‖GradeCore.ofCoreLinear (grade := grade) (vectorProjection parameters parameter inside state)‖ ≤
        constant * ‖GradeCore.ofCoreLinear (grade := grade) state‖ := by
  obtain ⟨axisC, axisC_nonneg, axisBound⟩ :=
    consumed_projection_bound (parameters := parameters) grade gradeLarge
  obtain ⟨outerC, outerC_nonneg, outerBound⟩ :=
    outerCorrection_norm_le parameters parameter inside grade (by omega)
  refine ⟨outerC * |triangularGradeConstant parameters parameter grade| * axisC,
    mul_nonneg (mul_nonneg outerC_nonneg (abs_nonneg _)) axisC_nonneg, ?_⟩
  intro state
  have gaugeBound : ∀ field : ACore parameters 3,
      ‖GradeCore.ofCoreLinear (grade := grade)
          (triangularGaugeProjection parameters parameter inside field)‖ ≤
        |triangularGradeConstant parameters parameter grade| *
          ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
    intro field
    rw [ofCoreLinear_norm_coordinates, ofCoreLinear_norm_coordinates]
    exact (triangularGaugeProjection_coordinates_bound parameters parameter inside field).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have axisNorm : ‖GradeCore.ofCoreLinear (grade := grade) (axisJetProjection state)‖ ≤
      axisC * ‖GradeCore.ofCoreLinear (grade := grade) state‖ := axisBound state
  rw [vectorProjection_apply]
  calc ‖GradeCore.ofCoreLinear (grade := grade) (outerCorrection parameters parameter inside
        (triangularGaugeProjection parameters parameter inside (axisJetProjection state)))‖
      ≤ outerC * ‖GradeCore.ofCoreLinear (grade := grade)
          (triangularGaugeProjection parameters parameter inside (axisJetProjection state))‖ :=
        outerBound _
    _ ≤ outerC * (|triangularGradeConstant parameters parameter grade| *
          ‖GradeCore.ofCoreLinear (grade := grade) (axisJetProjection state)‖) :=
        mul_le_mul_of_nonneg_left (gaugeBound _) outerC_nonneg
    _ ≤ outerC * (|triangularGradeConstant parameters parameter grade| *
          (axisC * ‖GradeCore.ofCoreLinear (grade := grade) state‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left axisNorm (abs_nonneg _)) outerC_nonneg
    _ = outerC * |triangularGradeConstant parameters parameter grade| * axisC *
          ‖GradeCore.ofCoreLinear (grade := grade) state‖ := by ring

end Grad.Cor18
