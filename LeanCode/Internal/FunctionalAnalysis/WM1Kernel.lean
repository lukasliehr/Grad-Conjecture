import WM1Tests
import MP1Calculus

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.WeakTesting
open Grad.WeakTesting.Commutation (HasWeakOrderedDerivative)
open scoped ContDiff

namespace Grad.Mollifier.WeakJets

theorem weakOrderedDerivative_integral (dimension rank : ℕ) (word : Fin rank → Fin 2)
    (field derivative : FieldL2 dimension Set.univ)
    (weakDerivative : HasWeakOrderedDerivative dimension Set.univ rank word field derivative)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test) :
    (∫ point : Spatial, test point • inner ℂ vector (derivative point cell)) =
      (-1 : ℂ) ^ rank * ∫ point : Spatial,
        orderedTestDerivative rank word test point • inner ℂ vector (field point cell) := by
  simpa only [compactPairing_apply, Grad.WeakTesting.Commutation.signedDerivativePairing,
    smul_apply, orderedDerivativePairing_apply, smul_eq_mul,
    Measure.restrict_univ] using
    weakDerivative cell vector test smoothness compactSupport (Set.subset_univ _)

theorem integral_cell_inner (dimension : ℕ) (function : Spatial → CellValues dimension)
    (kernel : Spatial → ℝ)
    (integrability : Integrable (fun point => kernel point • function point) volume)
    (cell : ℤ) (vector : PhysicalValue dimension) :
    inner ℂ vector ((∫ point : Spatial, kernel point • function point) cell) =
      ∫ point : Spatial, kernel point • inner ℂ vector (function point cell) := by
  let functional : CellValues dimension →L[ℝ] ℂ :=
    ((innerSL ℂ vector).comp (cellProjection (PhysicalValue dimension) cell)).restrictScalars ℝ
  change functional (∫ point : Spatial, kernel point • function point) = _
  rw [← functional.integral_comp_comm integrability]
  apply integral_congr_ae
  filter_upwards [] with point
  exact functional.map_smul (kernel point) (function point)

theorem reflected_sign_integral (rank : ℕ) (kernel : Spatial → ℝ) (pairing : Spatial → ℂ) :
    (-1 : ℂ) ^ rank * (∫ point : Spatial, ((-1 : ℝ) ^ rank * kernel point) • pairing point) =
      ∫ point : Spatial, kernel point • pairing point := by
  simp_rw [mul_smul]
  rw [integral_smul]
  have square : (-1 : ℂ) ^ rank * (-1 : ℂ) ^ rank = 1 := by
    rw [← mul_pow]
    simp
  change (-1 : ℂ) ^ rank * ((((-1 : ℝ) ^ rank : ℝ) : ℂ) *
    ∫ point : Spatial, kernel point • pairing point) = _
  push_cast
  rw [← mul_assoc, square, one_mul]

theorem kernelWeakGoal : KernelWeakGoal := by
  intro dimension rank word field derivative weakDerivative kernel smoothness compactSupport
  funext point
  have fieldCalculus := Pointwise.pointwiseGoal (CellValues dimension) kernel smoothness compactSupport field
  have derivativeCalculus :=
    Pointwise.pointwiseGoal (CellValues dimension) kernel smoothness compactSupport derivative
  refine (fieldCalculus.2.2 rank word point).2.trans ?_
  change (∫ source : Spatial, Pointwise.orderedDerivative rank word kernel (point - source) • field source) =
    ∫ source : Spatial, kernel (point - source) • derivative source
  apply lp.ext
  funext cell
  apply ext_inner_left ℂ
  intro vector
  rw [integral_cell_inner dimension field _ (fieldCalculus.2.2 rank word point).1 cell vector,
    integral_cell_inner dimension derivative _ (derivativeCalculus.1 point) cell vector]
  have identity := weakOrderedDerivative_integral dimension rank word field derivative weakDerivative
    cell vector (reflectedKernel point kernel) (reflectedKernel_contDiff point kernel smoothness)
      (reflectedKernel_compactSupport point kernel compactSupport)
  simp_rw [orderedTestDerivative_reflected rank word point kernel smoothness] at identity
  rw [reflected_sign_integral] at identity
  exact identity.symm

end Grad.Mollifier.WeakJets
