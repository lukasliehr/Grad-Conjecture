import AST7ActualSourceConsumer
import RadialIntegralJet
import ProductClosedSeries

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct Grad.RepresentedKernel.SpatialProduct

/-- Compact polynomial-weighted dilation, retaining the literal closed disk. -/
def powerDilationValue {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  ∫ scale in Icc (0 : ℝ) 1, scale ^ power • smoothClosedExtension field (scale • point)

theorem powerDilationValue_smooth {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (powerDilationValue power field) :=
  weightedIntegral_contDiff
    ((smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst))
    (fun scale : ℝ => scale ^ power) (continuous_id.pow power) 0 1

def powerDilationJet {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) : ClosedJet dimension :=
  globalClosedJet (powerDilationValue power field) (powerDilationValue_smooth power field)

theorem powerDilationJet_value {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) (point : ClosedDisk) :
    (powerDilationJet power field).value point =
      ∫ scale in Icc (0 : ℝ) 1, scale ^ power • smoothClosedExtension field (scale • point.val) := rfl

theorem powerDilationJet_derivative {dimension order : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (powerDilationJet power field) order word point =
      ∫ scale in Icc (0 : ℝ) 1, scale ^ (power + order) •
        cartesianDerivative order word (smoothClosedExtension field) (scale • point.val) := by
  rw [powerDilationJet, globalClosedJet_derivative]
  unfold powerDilationValue
  rw [cartesianDerivative_weightedIntegral order word
    (field := fun argument : SpatialPlane × ℝ => smoothClosedExtension field (argument.2 • argument.1))
    ((smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst))
    (fun scale : ℝ => scale ^ power) (continuous_id.pow power) 0 1]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale _
  dsimp only
  rw [cartesianDerivative_dilation scale _ (smoothClosedExtension_smooth field), smul_smul, ← pow_add]

theorem powerDilationJet_value_eq {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) :
    (powerDilationJet power field).value =
      ∫ scale in Icc (0 : ℝ) 1, scale ^ power • (dilationJet scale field).value := by
  have joint : Continuous (fun argument : ℝ × ClosedDisk =>
      argument.1 ^ power • smoothClosedExtension field (argument.1 • argument.2.val)) := by
    exact (continuous_fst.pow power).smul ((smoothClosedExtension_smooth field).continuous.comp
      (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))
  have continuousFamily : Continuous (fun scale : ℝ => scale ^ power • (dilationJet scale field).value) :=
    ContinuousMap.continuous_of_continuous_uncurry _ joint
  apply ContinuousMap.ext
  intro point
  rw [ContinuousMap.integral_apply continuousFamily.continuousOn.integrableOn_Icc]
  rfl

theorem powerDilationJet_add {dimension : ℕ} (power : ℕ) (first second : ClosedJet dimension) :
    powerDilationJet power (first + second) = powerDilationJet power first + powerDilationJet power second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have firstIntegrable : IntegrableOn (fun scale : ℝ => scale ^ power • smoothClosedExtension first (scale • point.val)) (Icc 0 1) :=
    ((continuous_id.pow power).smul ((smoothClosedExtension_smooth first).continuous.comp
      (continuous_id.smul continuous_const))).continuousOn.integrableOn_Icc
  have secondIntegrable : IntegrableOn (fun scale : ℝ => scale ^ power • smoothClosedExtension second (scale • point.val)) (Icc 0 1) :=
    ((continuous_id.pow power).smul ((smoothClosedExtension_smooth second).continuous.comp
      (continuous_id.smul continuous_const))).continuousOn.integrableOn_Icc
  change (∫ scale in Icc (0 : ℝ) 1, scale ^ power • smoothClosedExtension (first + second) (scale • point.val)) =
    (∫ scale in Icc (0 : ℝ) 1, scale ^ power • smoothClosedExtension first (scale • point.val)) +
    (∫ scale in Icc (0 : ℝ) 1, scale ^ power • smoothClosedExtension second (scale • point.val))
  rw [← integral_add firstIntegrable secondIntegrable]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  dsimp only
  have firstValue := smoothClosedExtension_value first (dilationPoint scale inside.1 inside.2 point)
  have secondValue := smoothClosedExtension_value second (dilationPoint scale inside.1 inside.2 point)
  have sumValue := smoothClosedExtension_value (first + second) (dilationPoint scale inside.1 inside.2 point)
  change smoothClosedExtension (first + second) (scale • point.val) =
    first.value (dilationPoint scale inside.1 inside.2 point) + second.value (dilationPoint scale inside.1 inside.2 point) at sumValue
  have valueEquality := sumValue.trans (congrArg₂ (fun first second => first + second) firstValue.symm secondValue.symm)
  exact (congrArg (fun value => scale ^ power • value) valueEquality).trans (smul_add _ _ _)

end Grad.ActualCenterVolterra
