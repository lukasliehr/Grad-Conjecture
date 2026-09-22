import GC18APWeights
import FC3Coordinates

noncomputable section

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.AnalyticWeights.Calculus

/-- The original phase W_n(Y)=exp(Phi_n(ell Y)), with no change of width. -/
def apWeightedJet {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) : ClosedJet dimension :=
  smoothScalarWeightedJet (physicalWeight sigma gamma ell cell)
    ((smoothGoal sigma gamma ell cell).2.1) field

theorem apWeightedJet_value {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    (apWeightedJet sigma gamma ell cell field).value point =
      originalWeight sigma gamma ell cell point.val • field.value point := rfl

def apWeightedJetLinear {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := apWeightedJet sigma gamma ell cell
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change physicalWeight sigma gamma ell cell point.val • (first.value point + second.value point) =
      physicalWeight sigma gamma ell cell point.val • first.value point +
        physicalWeight sigma gamma ell cell point.val • second.value point
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change physicalWeight sigma gamma ell cell point.val • (scalar • field.value point) =
      scalar • (physicalWeight sigma gamma ell cell point.val • field.value point)
    exact smul_comm _ _ _

/-- One literal AP2 coordinate. The input frequency is kappa, not lambda. -/
def apDerivativeL2 {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (index : DerivativeIndex grade) : ClosedJet dimension →ₗ[ℂ] DiskL2 dimension :=
  ((scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index)) •
    (closedDerivativeL2 (derivativeMultiIndex index)).comp (apWeightedJetLinear sigma gamma ell cell)

abbrev APRow (dimension grade : ℕ) := PiLp 2 (fun _ : DerivativeIndex grade => DiskL2 dimension)

abbrev APAmbient (dimension grade : ℕ) := lp (fun _ : ℤ => APRow dimension grade) 2

def apRowLinear {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) :
    ClosedJet dimension →ₗ[ℂ] APRow dimension grade where
  toFun field := WithLp.toLp 2 (fun index => apDerivativeL2 L sigma gamma ell cell index field)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (apDerivativeL2 L sigma gamma ell cell index).map_add first second
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact (apDerivativeL2 L sigma gamma ell cell index).map_smul scalar field

theorem apRowLinear_apply {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    apRowLinear L sigma gamma ell cell field index =
      (scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index) •
        closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma ell cell field) := rfl

theorem apRowLinear_norm_sq {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 =
      ∑ index : DerivativeIndex grade,
        scaledCellWeight L ell cell ^ (2 * (grade - derivativeOrder index)) *
          ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma ell cell field)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro index _
  rw [apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
  ring

def apSingle {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) : APAmbient dimension grade :=
  lp.single 2 cell (apRowLinear L sigma gamma ell cell field)

/-- Finite Fourier sums of genuine smooth closed jets, with the exact AP2
array. Its closure is the stated completed cap space, not an auxiliary norm. -/
def apSmoothCore (L sigma gamma ell : ℝ) (dimension grade : ℕ) : Submodule ℂ (APAmbient dimension grade) :=
  Submodule.span ℂ (Set.range fun pair : ℤ × ClosedJet dimension => apSingle L sigma gamma ell pair.1 pair.2)

def apGrade (L sigma gamma ell : ℝ) (dimension grade : ℕ) : Submodule ℂ (APAmbient dimension grade) :=
  (apSmoothCore L sigma gamma ell dimension grade).topologicalClosure

instance apGrade_complete (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    CompleteSpace (apGrade L sigma gamma ell dimension grade) := by
  unfold apGrade
  infer_instance

def apCoreInclusion (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    apSmoothCore L sigma gamma ell dimension grade →ₗᵢ[ℂ] apGrade L sigma gamma ell dimension grade where
  toLinearMap :=
    { toFun := fun core => ⟨core.val, Submodule.le_topologicalClosure _ core.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' _ := rfl

theorem apGrade_norm_sq (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖field‖ ^ 2 = ∑' cell : ℤ, ∑ index : DerivativeIndex grade, ‖field.val cell index‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field.val
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at normFormula
  rw [normFormula]
  apply tsum_congr
  intro cell
  rw [PiLp.norm_sq_eq_of_L2]

end Grad.GaugeCoefficients.Physical.RadialLedger
