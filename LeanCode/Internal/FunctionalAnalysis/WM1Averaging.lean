import WM1Independent
import T1Proof

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeakTesting Grad.SpatialTranslation
open scoped BigOperators ContDiff

namespace Grad.Mollifier.WeakJets

universe valueUniverse otherUniverse

theorem valueMap_average (Value : Type valueUniverse) (Other : Type otherUniverse)
    [NormedAddCommGroup Value] [InnerProductSpace ℂ Value] [CompleteSpace Value]
    [NormedAddCommGroup Other] [InnerProductSpace ℂ Other] [CompleteSpace Other]
    (mapping : Value →L[ℂ] Other) (kernel : Spatial → ℝ) (integrability : Integrable kernel volume)
    (field : DomainL2 Value Set.univ) :
    valueMap Value Other mapping (average Value kernel field) =
      average Other kernel (valueMap Value Other mapping field) := by
  have commutation := ((valueMap Value Other mapping).integral_comp_comm
    (kernel_integrand_integrable Value kernel integrability field)).symm
  refine commutation.trans ?_
  change (∫ offset : Spatial, valueMap Value Other mapping (kernel offset • translation Value offset field)) =
    ∫ offset : Spatial, kernel offset • translation Other offset (valueMap Value Other mapping field)
  apply integral_congr_ae
  filter_upwards [] with offset
  rw [LinearMapClass.map_smul_of_tower, translation_natural]

theorem cellNaturalityGoal : CellNaturalityGoal := by
  intro dimension kernel integrability
  exact ⟨fun field cell => valueMap_average (CellValues dimension) (PhysicalValue dimension)
    (cellProjection (PhysicalValue dimension) cell) kernel integrability field,
    fun weight field => valueMap_average (CellValues dimension) (CellValues dimension)
      (Grad.CellWeights.inverseCellCLM (PhysicalValue dimension) weight) kernel integrability field⟩

theorem averagedWeakGoal : AveragedWeakGoal := by
  intro dimension rank word field derivative weakDerivative kernel integrability
    cell vector test smoothness compactSupport supported
  rw [(functional_average (CellValues dimension) kernel integrability
    (compactPairing dimension Set.univ cell vector test smoothness compactSupport) derivative).2,
    (functional_average (CellValues dimension) kernel integrability
      (Grad.WeakTesting.Commutation.signedDerivativePairing dimension Set.univ cell vector test
        smoothness compactSupport rank word) field).2]
  apply integral_congr_ae
  filter_upwards [] with offset
  rw [translationWeakGoal dimension rank word field derivative weakDerivative offset
    cell vector test smoothness compactSupport supported]

theorem averageTuple_apply (dimension order : ℕ) (kernel : Spatial → ℝ)
    (tuple : JetTuple dimension order Set.univ) (index : JetIndex order) :
    averageTuple dimension order kernel tuple index = average (CellValues dimension) kernel (tuple index) := rfl

theorem averageTuple_base (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ) (integrability : Integrable kernel volume)
    (tuple : JetTuple dimension order Set.univ) :
    ambientBase dimension order Set.univ exponent (averageTuple dimension order kernel tuple) =
      average (CellValues dimension) kernel (ambientBase dimension order Set.univ exponent tuple) :=
  (cellNaturalityGoal dimension kernel integrability).2 (exponent (zeroIndex order)) (tuple (zeroIndex order))

theorem averageTuple_norm_le (dimension order : ℕ) (kernel : Spatial → ℝ)
    (tuple : JetTuple dimension order Set.univ) :
    ‖averageTuple dimension order kernel tuple‖ ≤ kernelL1 kernel * ‖tuple‖ := by
  have squared : ‖averageTuple dimension order kernel tuple‖ ^ 2 ≤ (kernelL1 kernel * ‖tuple‖) ^ 2 := by
    rw [tuple_norm_sq, mul_pow, tuple_norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    simpa only [averageTuple_apply, mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (average_norm_le (CellValues dimension) kernel (tuple index)) 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (kernelL1_nonneg kernel) (norm_nonneg _))).mp squared

theorem ambientGoal : AmbientGoal := by
  intro dimension order kernel integrability tuple
  exact ⟨averageTuple_apply dimension order kernel tuple,
    fun exponent => averageTuple_base dimension order exponent kernel integrability tuple,
    tuple_norm_sq dimension order Set.univ (averageTuple dimension order kernel tuple),
    averageTuple_norm_le dimension order kernel tuple⟩

def ambientAveraging (dimension order : ℕ) (kernel : Spatial → ℝ)
    (integrability : Integrable kernel volume) :
    JetTuple dimension order Set.univ →L[ℂ] JetTuple dimension order Set.univ :=
  ({ toFun := averageTuple dimension order kernel
     map_add' := fun first second => PiLp.ext fun index =>
       average_add (CellValues dimension) kernel integrability (first index) (second index)
     map_smul' := fun scalar tuple => PiLp.ext fun index =>
       average_smul (CellValues dimension) kernel scalar (tuple index) } :
      JetTuple dimension order Set.univ →ₗ[ℂ] JetTuple dimension order Set.univ).mkContinuous
    (kernelL1 kernel) (averageTuple_norm_le dimension order kernel)

theorem ambientAveraging_apply (dimension order : ℕ) (kernel : Spatial → ℝ)
    (integrability : Integrable kernel volume) (tuple : JetTuple dimension order Set.univ) :
    ambientAveraging dimension order kernel integrability tuple = averageTuple dimension order kernel tuple := rfl

end Grad.Mollifier.WeakJets
