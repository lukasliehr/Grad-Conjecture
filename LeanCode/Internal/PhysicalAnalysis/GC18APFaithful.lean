import GC18APWeakCore
import GC18APCoordinates

noncomputable section

set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GenericCarriers

def apIndexWord {grade : ℕ} (index : DerivativeIndex grade) : CartesianWord (derivativeOrder index) :=
  cartesianMultiIndexWord (derivativeMultiIndex index)

theorem apCompleted_weak {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (index : DerivativeIndex grade) (field : apGrade L sigma gamma ell dimension grade)
    (testCell : ℤ) (vector : PhysicalValue dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing dimension testCell vector test smooth compact (apUnscaledCoordinate L sigma gamma ell cell index field) =
      (-1 : ℂ) ^ derivativeOrder index *
        apDiskDerivativePairing dimension testCell vector test smooth compact (derivativeOrder index) (apIndexWord index)
          (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq
      ((apDiskPairing dimension testCell vector test smooth compact).continuous.comp
        (apUnscaledCoordinate L sigma gamma ell cell index).continuous)
      (continuous_const.mul ((apDiskDerivativePairing dimension testCell vector test smooth compact
        (derivativeOrder index) (apIndexWord index)).continuous.comp
          (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade)).continuous))) _ field
  intro core
  simp only [Function.comp_apply, Pi.mul_apply]
  rw [apUnscaledCoordinate_core, apUnscaledCoordinate_core]
  change apDiskPairing dimension testCell vector test smooth compact
    (closedContinuousToDiskL2 (closedDerivative (apWeightedJet sigma gamma ell cell (core cell))
      (derivativeOrder index) (apIndexWord index))) =
    (-1 : ℂ) ^ derivativeOrder index * apDiskDerivativePairing dimension testCell vector test smooth compact
      (derivativeOrder index) (apIndexWord index)
        (closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell cell (core cell)) (0, 0)))
  rw [closedMultiDerivative_zero]
  exact apClosedJet_weak (apWeightedJet sigma gamma ell cell (core cell)) (apIndexWord index)
    testCell vector test smooth compact supported

/-- Faithfulness of the original AP2 completed graph is obtained from
literal compact-test weak derivatives, not inferred from its core alone. -/
theorem apGrade_eq_zero_of_base_zero {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (field : apGrade L sigma gamma ell dimension grade)
    (baseZero : ∀ cell, apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) field = 0) : field = 0 := by
  have derivativesZero (cell : ℤ) (index : DerivativeIndex grade) :
      apUnscaledCoordinate L sigma gamma ell cell index field = 0 := by
    apply apDiskPairing_separates
    intro testCell vector test smooth compact supported
    rw [apCompleted_weak L sigma gamma ell cell index field testCell vector test smooth compact supported,
      baseZero, map_zero, mul_zero, map_zero]
  apply Subtype.ext
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro index
  rw [apCoordinate_eq_scaled, derivativesZero, smul_zero]
  rfl

theorem apGrade_ext {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (first second : apGrade L sigma gamma ell dimension grade)
    (equalities : ∀ cell, apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) first =
      apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) second) : first = second := by
  apply sub_eq_zero.mp
  apply apGrade_eq_zero_of_base_zero
  intro cell
  rw [map_sub, equalities, sub_self]

end Grad.GaugeCoefficients.Physical.RadialLedger
