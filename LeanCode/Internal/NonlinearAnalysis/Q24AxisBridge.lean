import Q24RootAgreement
import QT6ActualCompletions
import TameChartGoal

noncomputable section

open scoped BigOperators

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.AxisCore
open Grad.Q8FixedGrade Grad.RealFixedRanges

/-- The two existing axis cores use exactly the same weighted square terms. -/
theorem tangentTerm_eq_axis (parameters : PhaseParameters) (grade : ℕ)
    (family : ℤ → ComplexEuclidean 2) (cell : ℤ) :
    tangentNormTerm parameters grade family cell =
      axisWeight parameters grade cell ^ 2 * ‖family cell‖ ^ 2 := by
  unfold tangentNormTerm axisWeight
  simp only [mul_pow, ← pow_mul, Nat.mul_comm grade 2]

def tangentAxisEquiv (parameters : PhaseParameters) :
    TangentCoefficient parameters ≃ₗ[ℂ] AxisSmoothCore parameters 2 where
  toFun family := ⟨family.val, fun grade =>
    (family.property grade).congr (fun cell => tangentTerm_eq_axis parameters grade family.val cell)⟩
  invFun family := ⟨family.val, fun grade =>
    (family.property grade).congr (fun cell => (tangentTerm_eq_axis parameters grade family.val cell).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identical tangential coefficients embedded in the original axis grade. -/
def tangentToGrade (parameters : PhaseParameters) (grade : ℕ) :
    TangentCoefficient parameters →ₗ[ℂ] AxisGrade parameters 2 grade :=
  (axisEta parameters 2 grade).comp (tangentAxisEquiv parameters).toLinearMap

theorem tangentToGrade_norm (parameters : PhaseParameters) (grade : ℕ)
    (family : TangentCoefficient parameters) :
    ‖tangentToGrade parameters grade family‖ = tangentNorm grade family := by
  rw [tangentNorm, ← Real.sqrt_sq (norm_nonneg (tangentToGrade parameters grade family))]
  congr 1
  rw [tangentToGrade, LinearMap.comp_apply, axisEta_norm_sq]
  exact tsum_congr (fun cell => (tangentTerm_eq_axis parameters grade family.val cell).symm)

theorem tangentToGrade_injective (parameters : PhaseParameters) (grade : ℕ) :
    Function.Injective (tangentToGrade parameters grade) := by
  intro first second equality
  apply (tangentAxisEquiv parameters).injective
  exact axisEta_injective parameters 2 grade _ _ equality

theorem tangentToGrade_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (tangentToGrade parameters grade) := by
  rw [Metric.denseRange_iff]
  intro target epsilon positive
  obtain ⟨core, _, close⟩ := axis_finite_support_dense parameters 2 grade target epsilon positive
  refine ⟨(tangentAxisEquiv parameters).symm core, ?_⟩
  change dist target (axisEta parameters 2 grade
    ((tangentAxisEquiv parameters) ((tangentAxisEquiv parameters).symm core))) < epsilon
  rw [LinearEquiv.apply_symm_apply, dist_eq_norm]
  exact close

/-- The existing smoothing-state axis core is the same coefficient core. -/
def smoothingToTangent (parameters : PhaseParameters) :
    Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2) →ₗ[ℂ]
      TangentCoefficient parameters where
  toFun family := (tangentAxisEquiv parameters).symm
    ⟨family.val, fun grade => by
      have summable := (memlp_iff_summable_sq _).mp (family.property grade)
      apply summable.congr
      intro cell
      change ‖(axisWeight parameters grade cell : ℂ) • family.val cell‖ ^ 2 = _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (axisWeight_pos parameters grade cell), mul_pow]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tangentToGrade_smoothing (parameters : PhaseParameters) (grade : ℕ)
    (family : Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2)) :
    tangentToGrade parameters grade (smoothingToTangent parameters family) =
      Grad.SmoothingFamily.axisToGrade parameters.sigma0 grade family := by
  apply lp.ext
  funext cell
  rfl

end Grad.Q24Realization
