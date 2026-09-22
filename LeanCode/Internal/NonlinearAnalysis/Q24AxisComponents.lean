import Q24AxisBridge

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.AxisCore
open Grad.Q8FixedGrade Grad.RealFixedRanges

abbrev TangentGradeCore (parameters : PhaseParameters) (grade : ℕ) :=
  NormedCoreCopy ((tangentToGrade parameters grade).restrictScalars ℝ)
    (tangentToGrade_injective parameters grade)

-- Explicit specialization avoids a typeclass transparency failure at the
-- scalar-restricted embedding; all structures are the accepted induced ones.
instance {parameters : PhaseParameters} {grade : ℕ} :
    NormedAddCommGroup (TangentGradeCore parameters grade) :=
  NormedCoreCopy.instNormedAddCommGroup
    (embedding := (tangentToGrade parameters grade).restrictScalars ℝ)
    (injective := tangentToGrade_injective parameters grade)

instance {parameters : PhaseParameters} {grade : ℕ} :
    Module ℝ (TangentGradeCore parameters grade) :=
  NormedCoreCopy.instModuleReal
    (embedding := (tangentToGrade parameters grade).restrictScalars ℝ)
    (injective := tangentToGrade_injective parameters grade)

instance {parameters : PhaseParameters} {grade : ℕ} :
    NormedSpace ℝ (TangentGradeCore parameters grade) :=
  NormedCoreCopy.instNormedSpaceReal
    (embedding := (tangentToGrade parameters grade).restrictScalars ℝ)
    (injective := tangentToGrade_injective parameters grade)

def tangentGradeEmbedding (parameters : PhaseParameters) (grade : ℕ) :
    TangentGradeCore parameters grade →ₗᵢ[ℝ] AxisGrade parameters 2 grade :=
  NormedCoreCopy.isometricEmbedding _ _

theorem tangentGradeEmbedding_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (tangentGradeEmbedding parameters grade) :=
  NormedCoreCopy.isometricEmbedding_denseRange (tangentToGrade_denseRange parameters grade)

def tangentComponentCoreLinear (parameters : PhaseParameters) (grade : ℕ) (index : Fin 2) :
    TangentGradeCore parameters (grade + 1) →ₗ[ℝ] Carrier parameters grade where
  toFun family := embed parameters grade (tangentComponent family.toCore index)
  map_add' first second := by
    change embed parameters grade (tangentComponent (first.toCore + second.toCore) index) = _
    rw [tangentComponent_add, map_add]
  map_smul' scalar family := by
    change embed parameters grade (tangentComponent ((scalar : ℂ) • family.toCore) index) = _
    rw [tangentComponent_smul, map_smul]
    rfl

def tangentComponentCore (parameters : PhaseParameters) (grade : ℕ) (index : Fin 2) :
    TangentGradeCore parameters (grade + 1) →L[ℝ] Carrier parameters grade :=
  (tangentComponentCoreLinear parameters grade index).mkContinuous
    (Real.sqrt 2 ^ grade * axisConstant) (fun family => by
      change ‖embed parameters grade (tangentComponent family.toCore index)‖ ≤ _
      rw [embed_norm]
      have bound := (tangentComponent_envelope_le grade family.toCore index).trans
        (tangentPlanarEnvelope_le grade family.toCore)
      change _ ≤ (Real.sqrt 2 ^ grade * axisConstant) *
        ‖tangentToGrade parameters (grade + 1) family.toCore‖
      rw [tangentToGrade_norm]
      exact bound.trans_eq (mul_assoc _ _ _).symm)

/-- Each axis component has its actual continuous extension to the fixed-grade
Q8 coefficient completion, using the original q+1 axis shift. -/
def tangentComponentMap (parameters : PhaseParameters) (grade : ℕ) (index : Fin 2) :
    AxisGrade parameters 2 (grade + 1) →L[ℝ] Carrier parameters grade :=
  (tangentComponentCore parameters grade index).extend
    (tangentGradeEmbedding parameters (grade + 1)).toContinuousLinearMap

theorem tangentComponentMap_core (parameters : PhaseParameters) (grade : ℕ) (index : Fin 2)
    (family : TangentCoefficient parameters) :
    tangentComponentMap parameters grade index (tangentToGrade parameters (grade + 1) family) =
      embed parameters grade (tangentComponent family index) :=
  ContinuousLinearMap.extend_eq _ (tangentGradeEmbedding_denseRange parameters (grade + 1))
    (tangentGradeEmbedding parameters (grade + 1)).isometry.isUniformInducing
    (NormedCoreCopy.ofCore _ _ family)

end Grad.Q24Realization
