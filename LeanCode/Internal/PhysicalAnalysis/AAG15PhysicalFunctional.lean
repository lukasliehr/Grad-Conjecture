import AAG9CompletedSharpTrace
import AAG13PhysicalTestMultipliers
import AAR1ActualBulkRecovery

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularVariational

open Grad.CartesianState Grad.AnnularReconstruction

instance annularBoundary_realInner : InnerProductSpace ℝ AnnularBoundary :=
  InnerProductSpace.rclikeToReal ℂ AnnularBoundary

/-- Conjugated undifferentiated f,G3,F2 and the natural normalized outer
datum nu^(-1/2) D e^Phi beta. Each bulk component uses literal r dr. -/
abbrev AnnularForcing (lower : ℝ) :=
  AnnularBulk lower × (AnnularBulk lower × (AnnularBulk lower × AnnularBoundary))

theorem annularEnergyD_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) : ‖annularEnergyD lower length positive field‖ ≤ ‖field‖ := by
  calc
    _ ≤ 1 * ‖annularEnergyMass lower length positive field‖ :=
      complexLpTwoMap_bound (fun mode : HighAnnularMode => annularImaginarySymbolMap lower length positive mode
        ((mode.val.1 : ℝ) * Grad.CircularHighWeak.highMultiplier mode.val.1)
        (annularDSymbol_dominated lower length positive mode)) 1 (by norm_num)
        (fun mode => annularImaginarySymbolMap_bound lower length positive mode _ _)
        (annularEnergyMass lower length positive field)
    _ ≤ _ := by rw [one_mul]; exact annularEnergyMass_bound lower length positive field

theorem annularEnergyCell_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) : ‖annularEnergyCell lower length positive field‖ ≤ ‖field‖ := by
  calc
    _ ≤ 1 * ‖annularEnergyMass lower length positive field‖ :=
      complexLpTwoMap_bound (fun mode : HighAnnularMode => annularImaginarySymbolMap lower length positive mode
        (Grad.CircularHighWeak.highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length)
        (annularCellSymbol_dominated lower length positive mode)) 1 (by norm_num)
        (fun mode => annularImaginarySymbolMap_bound lower length positive mode _ _)
        (annularEnergyMass lower length positive field)
    _ ≤ _ := by rw [one_mul]; exact annularEnergyMass_bound lower length positive field

theorem annularEnergyTrace_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (endpoint : Fin 2) (field : annularEnergySpace lower length positive) :
    ‖annularEnergyTrace lower length positive bounded lengthPositive endpoint field‖ ≤
      annularTraceConstant lower length * ‖field‖ :=
  ((annularEnergyTrace lower length positive bounded lengthPositive endpoint).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right
      (annularEnergyTrace_exists lower length positive bounded lengthPositive endpoint).choose_spec.2 (norm_nonneg _))

section Functional
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularSourceTest : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  annularEnergyDerivative lower length positive +
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength +
    annularEnergyRadial lower length positive

theorem annularSourceTest_bound (field : annularEnergySpace lower length positive) :
    ‖annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤ 3 * ‖field‖ := by
  have first := annularEnergyDerivative_bound lower length positive field
  have second := annularEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength field
  have third := annularEnergyRadial_bound lower length positive field
  have triangle := (norm_add_le
    (annularEnergyDerivative lower length positive field +
      annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
    (annularEnergyRadial lower length positive field)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  change ‖annularEnergyDerivative lower length positive field +
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field +
    annularEnergyRadial lower length positive field‖ ≤ _
  nlinarith [norm_nonneg field]

/-- Exactly AG14; no derivative or endpoint evaluation of an L2 source is used. -/
def annularFunctionalValue (source : AnnularForcing lower) (test : annularEnergySpace lower length positive) : ℂ :=
  inner ℂ (annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) source.1 -
    inner ℂ (annularEnergyD lower length positive test) source.2.1 -
    inner ℂ (annularEnergyCell lower length positive test) source.2.2.1 -
    inner ℂ (annularEnergyTrace lower length positive bounded lengthPositive 1 test) source.2.2.2

def annularFunctional (source : AnnularForcing lower) : annularEnergySpace lower length positive →L[ℝ] ℝ :=
  (innerSL ℝ source.1).comp
      ((annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength).restrictScalars ℝ) -
    (innerSL ℝ source.2.1).comp ((annularEnergyD lower length positive).restrictScalars ℝ) -
    (innerSL ℝ source.2.2.1).comp ((annularEnergyCell lower length positive).restrictScalars ℝ) -
    (innerSL ℝ source.2.2.2).comp ((annularEnergyTrace lower length positive bounded lengthPositive 1).restrictScalars ℝ)

theorem annularFunctional_literal (source : AnnularForcing lower) (test : annularEnergySpace lower length positive) :
    annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source test =
      (annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test).re := by
  change (inner ℂ source.1 (annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength test)).re -
    (inner ℂ source.2.1 (annularEnergyD lower length positive test)).re -
    (inner ℂ source.2.2.1 (annularEnergyCell lower length positive test)).re -
    (inner ℂ source.2.2.2 (annularEnergyTrace lower length positive bounded lengthPositive 1 test)).re = _
  simp only [annularFunctionalValue, Complex.sub_re]
  exact congrArg₂ (fun first second : ℝ => first - second)
    (congrArg₂ (fun first second : ℝ => first - second)
      (congrArg₂ (fun first second : ℝ => first - second)
        (inner_re_symm (𝕜 := ℂ) _ _) (inner_re_symm (𝕜 := ℂ) _ _))
      (inner_re_symm (𝕜 := ℂ) _ _)) (inner_re_symm (𝕜 := ℂ) _ _)

theorem annularFunctionalValue_test_smul (source : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source (scalar • test) =
      (starRingEnd ℂ scalar) *
        annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test := by
  simp only [annularFunctionalValue, map_smul, inner_smul_left]
  ring

def annularForcingSize (source : AnnularForcing lower) : ℝ :=
  3 * ‖source.1‖ + ‖source.2.1‖ + ‖source.2.2.1‖ + annularTraceConstant lower length * ‖source.2.2.2‖

theorem annularFunctionalValue_bound (source : AnnularForcing lower) (test : annularEnergySpace lower length positive) :
    ‖annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test‖ ≤
      annularForcingSize lower length source * ‖test‖ := by
  have first := (norm_inner_le_norm (𝕜 := ℂ)
    (annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) source.1).trans
      (mul_le_mul_of_nonneg_right (annularSourceTest_bound parameters lower length positive lengthPositive widthHalf widthLength test)
        (norm_nonneg source.1))
  have second := (norm_inner_le_norm (𝕜 := ℂ) (annularEnergyD lower length positive test) source.2.1).trans
    (mul_le_mul_of_nonneg_right (annularEnergyD_bound lower length positive test) (norm_nonneg source.2.1))
  have third := (norm_inner_le_norm (𝕜 := ℂ) (annularEnergyCell lower length positive test) source.2.2.1).trans
    (mul_le_mul_of_nonneg_right (annularEnergyCell_bound lower length positive test) (norm_nonneg source.2.2.1))
  have fourth := (norm_inner_le_norm (𝕜 := ℂ) (annularEnergyTrace lower length positive bounded lengthPositive 1 test) source.2.2.2).trans
    (mul_le_mul_of_nonneg_right (annularEnergyTrace_bound lower length positive bounded lengthPositive 1 test) (norm_nonneg source.2.2.2))
  have triangle := (norm_sub_le
    (inner ℂ (annularSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) source.1 -
      inner ℂ (annularEnergyD lower length positive test) source.2.1 -
      inner ℂ (annularEnergyCell lower length positive test) source.2.2.1)
    (inner ℂ (annularEnergyTrace lower length positive bounded lengthPositive 1 test) source.2.2.2)).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  unfold annularFunctionalValue annularForcingSize
  nlinarith only [triangle, first, second, third, fourth]

end Functional

end Grad.AnnularVariational
