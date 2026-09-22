import Q24RootAgreement
import TameChartGoal
import TangentialCore

noncomputable section

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.NonlinearProduct

def fieldEmbed (parameters : PhaseParameters) (dimension grade : ℕ) :
    ACore parameters dimension →ₗ[ℂ] AGrade parameters dimension grade :=
  (aGradeEta parameters).toLinearMap.comp GradeCore.ofCoreLinear

theorem fieldEmbed_norm (parameters : PhaseParameters) (dimension grade : ℕ)
    (field : ACore parameters dimension) :
    ‖fieldEmbed parameters dimension grade field‖ = originalGradeNorm grade field :=
  aGradeEta_norm parameters (GradeCore.ofCoreLinear field)

def coefficientFieldLinear (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (field : ACore parameters dimension) :
    Grad.Q8FixedGrade.Core parameters grade →ₗ[ℂ] AGrade parameters dimension grade where
  toFun coefficient := fieldEmbed parameters dimension grade
    (tameScalarMultiplier dimension coefficient.toCore field)
  map_add' first second := by
    change fieldEmbed parameters dimension grade
      (tameScalarMultiplier dimension (first.toCore + second.toCore) field) = _
    rw [tameScalarMultiplier_add, map_add]
  map_smul' scalar coefficient := by
    change fieldEmbed parameters dimension grade
      (tameScalarMultiplier dimension (scalar • coefficient.toCore) field) = _
    rw [tameScalarMultiplier_smul, map_smul]
    rfl

def coefficientFieldCore (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (field : ACore parameters dimension) :
    Grad.Q8FixedGrade.Core parameters grade →L[ℂ] AGrade parameters dimension grade :=
  (coefficientFieldLinear parameters dimension grade field).mkContinuous
    (Grad.Constraints.Multipliers.multiplierConstant grade parameters.gamma * originalGradeNorm grade field)
    (fun coefficient => by
      change ‖fieldEmbed parameters dimension grade
        (tameScalarMultiplier dimension coefficient.toCore field)‖ ≤ _
      rw [fieldEmbed_norm]
      exact (tameScalarMultiplier_bound dimension coefficient.toCore field grade).trans_eq
        (by rw [Grad.Q8FixedGrade.core_norm]; ring))

/-- Scalar multiplication of a fixed actual smooth field, extended from the
literal coefficient core to its fixed-grade norm completion. -/
def coefficientFieldMap (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (field : ACore parameters dimension) :
    Grad.Q8FixedGrade.Carrier parameters grade →L[ℂ] AGrade parameters dimension grade :=
  (coefficientFieldCore parameters dimension grade field).fromCompletion

theorem coefficientFieldMap_core (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (field : ACore parameters dimension)
    (coefficient : TameCoefficient parameters) :
    coefficientFieldMap parameters dimension grade field
        (Grad.Q8FixedGrade.embed parameters grade coefficient) =
      fieldEmbed parameters dimension grade (tameScalarMultiplier dimension coefficient field) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ (Grad.Q8FixedGrade.Core.mk coefficient)

/-- The existing bounded value-map extension on the original field grades. -/
def fieldValueMap (parameters : PhaseParameters) {sourceDimension targetDimension : ℕ}
    (grade : ℕ) (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    AGrade parameters sourceDimension grade →L[ℂ] AGrade parameters targetDimension grade :=
  (Grad.Constraints.valueMapGradeCoreContinuous mapping parameters).completion

theorem fieldValueMap_core (parameters : PhaseParameters) {sourceDimension targetDimension : ℕ}
    (grade : ℕ) (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) :
    fieldValueMap parameters grade mapping (fieldEmbed parameters sourceDimension grade field) =
      fieldEmbed parameters targetDimension grade (valueMapCore parameters mapping field) := by
  rw [fieldValueMap, fieldEmbed, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    aGradeEta_apply, ContinuousLinearMap.completion_apply_coe]
  rfl

end Grad.Q24Realization
