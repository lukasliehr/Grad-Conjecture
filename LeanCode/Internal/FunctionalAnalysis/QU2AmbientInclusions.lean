import QU1AxisInclusions

noncomputable section

open scoped BigOperators

namespace Grad.ConstrainedGrades

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.SmoothingFamily
open Grad.ImplementationReadiness Grad.CompatibleCompletion Grad.QuotientProjection

theorem fieldLowering_norm_le {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : AGrade parameters dimension upper) :
    ‖completedInclusion parameters ordered field‖ ≤ ‖field‖ := by
  exact (completedInclusion parameters ordered).le_of_opNorm_le
    (completedInclusion_norm_le_one parameters ordered) field |>.trans_eq (one_mul _)

/-- Axis-(q+1), vector-q, scalar-q inclusion in the literal sum carrier. -/
def xLoweringLinear {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    XAmbient parameters upper →ₗ[ℂ] XAmbient parameters lower where
  toFun field := statePack
    (axisLowering parameters (Nat.add_le_add_right ordered 1) field.ofLp.1)
    (completedInclusion parameters ordered field.ofLp.2.ofLp.1)
    (completedInclusion parameters ordered field.ofLp.2.ofLp.2)
  map_add' first second := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact (axisLowering parameters (Nat.add_le_add_right ordered 1)).map_add _ _
    · apply (WithLp.equiv 1 _).injective
      exact Prod.ext ((completedInclusion parameters ordered).map_add _ _)
        ((completedInclusion parameters ordered).map_add _ _)
  map_smul' scalar field := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact (axisLowering parameters (Nat.add_le_add_right ordered 1)).map_smul scalar _
    · apply (WithLp.equiv 1 _).injective
      exact Prod.ext ((completedInclusion parameters ordered).map_smul scalar _)
        ((completedInclusion parameters ordered).map_smul scalar _)

theorem xLoweringLinear_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : XAmbient parameters upper) :
    ‖xLoweringLinear parameters ordered field‖ ≤ ‖field‖ := by
  change ‖statePack _ _ _‖ ≤ _
  rw [statePack_norm, xAmbient_norm]
  exact add_le_add (add_le_add
    (axisLowering_norm_le parameters (Nat.add_le_add_right ordered 1) field.ofLp.1)
    (fieldLowering_norm_le parameters ordered field.ofLp.2.ofLp.1))
    (fieldLowering_norm_le parameters ordered field.ofLp.2.ofLp.2)

def xLowering {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    XAmbient parameters upper →L[ℂ] XAmbient parameters lower :=
  (xLoweringLinear parameters ordered).mkContinuous 1
    (fun field => by simpa only [one_mul] using xLoweringLinear_norm_le parameters ordered field)

theorem xLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : XAmbient parameters upper) :
    ‖xLowering parameters ordered field‖ ≤ ‖field‖ := xLoweringLinear_norm_le parameters ordered field

theorem xLowering_core {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : StateCore parameters) :
    xLowering parameters ordered (stateToGrade parameters upper field) = stateToGrade parameters lower field := by
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · exact axisLowering_core parameters (Nat.add_le_add_right ordered 1) field.1
  · apply (WithLp.equiv 1 _).injective
    exact Prod.ext (completedInclusion_apply_eta parameters ordered (GradeCore.ofCoreLinear field.2.1))
      (completedInclusion_apply_eta parameters ordered (GradeCore.ofCoreLinear field.2.2))

theorem xLowering_injective {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    Function.Injective (xLowering parameters ordered) := by
  intro first second equality
  have axis := congrArg (fun field : XAmbient parameters lower => field.ofLp.1) equality
  have vector := congrArg (fun field : XAmbient parameters lower => field.ofLp.2.ofLp.1) equality
  have scalar := congrArg (fun field : XAmbient parameters lower => field.ofLp.2.ofLp.2) equality
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext (axisLowering_injective parameters (Nat.add_le_add_right ordered 1) axis)
  apply (WithLp.equiv 1 _).injective
  exact Prod.ext (completedInclusion_injective parameters ordered vector)
    (completedInclusion_injective parameters ordered scalar)

/-- Coordinatewise inclusion in the literal fourfold Hilbert carrier. -/
def zLoweringLinear {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    ZAmbient parameters upper →ₗ[ℂ] ZAmbient parameters lower where
  toFun field := WithLp.toLp 2 (fun coordinate => completedInclusion parameters ordered (field coordinate))
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    exact (completedInclusion parameters ordered).map_add _ _
  map_smul' scalar field := by
    apply PiLp.ext
    intro coordinate
    exact (completedInclusion parameters ordered).map_smul scalar _

theorem zLoweringLinear_apply {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : ZAmbient parameters upper) (coordinate : Fin 4) :
    zLoweringLinear parameters ordered field coordinate =
      completedInclusion parameters ordered (field coordinate) := rfl

theorem zLoweringLinear_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : ZAmbient parameters upper) :
    ‖zLoweringLinear parameters ordered field‖ ≤ ‖field‖ := by
  have squares : ‖zLoweringLinear parameters ordered field‖ ^ 2 ≤ ‖field‖ ^ 2 := by
    rw [zAmbient_norm_sq, zAmbient_norm_sq]
    apply Finset.sum_le_sum
    intro coordinate _
    exact pow_le_pow_left₀ (norm_nonneg _) (fieldLowering_norm_le parameters ordered (field coordinate)) 2
  nlinarith [norm_nonneg (zLoweringLinear parameters ordered field), norm_nonneg field]

def zLowering {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    ZAmbient parameters upper →L[ℂ] ZAmbient parameters lower :=
  (zLoweringLinear parameters ordered).mkContinuous 1
    (fun field => by simpa only [one_mul] using zLoweringLinear_norm_le parameters ordered field)

theorem zLowering_apply {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : ZAmbient parameters upper) (coordinate : Fin 4) :
    zLowering parameters ordered field coordinate = completedInclusion parameters ordered (field coordinate) := rfl

theorem zLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : ZAmbient parameters upper) :
    ‖zLowering parameters ordered field‖ ≤ ‖field‖ := zLoweringLinear_norm_le parameters ordered field

theorem zLowering_core {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : SmoothQuotient parameters) :
    zLowering parameters ordered (quotientEta parameters upper field) = quotientEta parameters lower field := by
  apply PiLp.ext
  intro coordinate
  exact completedInclusion_apply_eta parameters ordered (GradeCore.ofCoreLinear (field coordinate))

theorem zLowering_injective {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    Function.Injective (zLowering parameters ordered) := by
  intro first second equality
  apply PiLp.ext
  intro coordinate
  exact completedInclusion_injective parameters ordered (congrArg (fun field => field coordinate) equality)

end Grad.ConstrainedGrades
