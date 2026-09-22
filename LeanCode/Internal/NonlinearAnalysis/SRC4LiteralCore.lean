import SRC3CompletedComponents
import SC8PublicBoundary

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.SourceCollarBulk

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarAngular Grad.FlatSourceProjection
open Grad.SourceCollar Grad.Constraints.Gauges
open Grad.Constraints

/-- Exact all-row smooth-core formula for `F0`. Every
`restrictionModeLp` on the right is literally `nu^(t+1)` times the radial
Fourier coefficient of `W f`, with `W` inside `radialIter`. -/
theorem completedForceTangential_core_row
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (source : SmoothQuotient parameters) (index : Fin 2) (mode : ℤ × ℤ) :
    (completedForceTangential lower positive bounded parameters tangential
      (quotientEta parameters (tangential + 2) source)).val index mode =
      radialValueMap lower (planarComponentMap 1)
        ((2 : ℂ)⁻¹ •
          (annularShiftScalar (tangential + 1) 1 mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 - 1, mode.2) +
            annularShiftScalar (tangential + 1) (-1) mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 + 1, mode.2))) -
      radialValueMap lower (planarComponentMap 0)
        ((2 * Complex.I : ℂ)⁻¹ •
          (annularShiftScalar (tangential + 1) 1 mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 - 1, mode.2) -
            annularShiftScalar (tangential + 1) (-1) mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 + 1, mode.2))) := by
  rw [completedForceTangential_core]
  exact annularTangentialContraction_restriction_core lower positive bounded parameters
    (tangential + 1) 1 (GradeCore.ofCoreLinear (cartesianSourceVector source)) index mode

/-- Exact all-row smooth-core formula for `F1`, with the same literal
weighted radial derivatives. -/
theorem completedForceRadial_core_row
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (source : SmoothQuotient parameters) (index : Fin 2) (mode : ℤ × ℤ) :
    (completedForceRadial lower positive bounded parameters tangential
      (quotientEta parameters (tangential + 2) source)).val index mode =
      radialValueMap lower (planarComponentMap 0)
        ((2 : ℂ)⁻¹ •
          (annularShiftScalar (tangential + 1) 1 mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 - 1, mode.2) +
            annularShiftScalar (tangential + 1) (-1) mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 + 1, mode.2))) +
      radialValueMap lower (planarComponentMap 1)
        ((2 * Complex.I : ℂ)⁻¹ •
          (annularShiftScalar (tangential + 1) 1 mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 - 1, mode.2) -
            annularShiftScalar (tangential + 1) (-1) mode •
              restrictionModeLp lower (tangential + 1) index.val parameters
                (cartesianSourceVector source) (mode.1 + 1, mode.2))) := by
  rw [completedForceRadial_core]
  exact annularRadialContraction_restriction_core lower positive bounded parameters
    (tangential + 1) 1 (GradeCore.ofCoreLinear (cartesianSourceVector source)) index mode

/-- Exact all-row smooth-core formula for `F2=h/L`. -/
theorem completedFourthSource_core_row
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (tangential : ℕ)
    (source : SmoothQuotient parameters) (index : Fin 2) (mode : ℤ × ℤ) :
    (completedFourthSource lower positive bounded parameters L tangential
      (quotientEta parameters (tangential + 2) source)).val index mode =
      (L : ℂ)⁻¹ • restrictionModeLp lower tangential index.val parameters
        (source 3) mode := by
  have result := congrArg
    (fun value : annularDerivativeGraph 1 lower positive 1 => value.val index mode)
    (completedFourthSource_core lower positive bounded parameters L tangential source)
  have scalarEvaluation :
      (((L : ℂ)⁻¹ • completedRestriction lower positive bounded parameters tangential 1
          (aGradeEta parameters (GradeCore.ofCoreLinear (source 3)))).val index mode) =
        (L : ℂ)⁻¹ •
          (completedRestriction lower positive bounded parameters tangential 1
            (aGradeEta parameters (GradeCore.ofCoreLinear (source 3)))).val index mode := by
    rfl
  exact result.trans (scalarEvaluation.trans (congrArg ((L : ℂ)⁻¹ • ·)
    (completedRestriction_core lower positive bounded parameters tangential 1
      (GradeCore.ofCoreLinear (source 3)) index mode)))

/-- The `R F0` graph is genuinely the diagonal angular derivative of every
value and weak radial-derivative row. -/
theorem completedForceAngular_core_row
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (source : SmoothQuotient parameters) (index : Fin 2) (mode : ℤ × ℤ) :
    (completedForceAngular lower positive bounded parameters tangential
      (quotientEta parameters (tangential + 2) source)).val index mode =
      annularAngularRatio mode •
        (completedForceTangential lower positive bounded parameters tangential
          (quotientEta parameters (tangential + 2) source)).val index mode := rfl

/-- The primitive restriction row is exactly the weighted radial Fourier
coefficient with the Cartesian phase `W` applied before every radial
derivative. -/
theorem restrictionModeLp_weighted_core_ae {dimension : ℕ}
    (lower : ℝ) (_positive : 0 < lower)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      restrictionModeLp lower power radial parameters field mode radius =
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
          (Real.sqrt radius •
            radialCoefficientJet
              (originalPolarValue
                (phaseWeightedJet parameters mode.2 (field.val mode.2)))
              mode.1 radial radius) := by
  unfold restrictionModeLp
  filter_upwards [Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ) ^ power)
      (radialToLp lower
        (radialCoefficientJet
          (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
          mode.1 radial)
        (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous),
    radialToLp_ae lower
      (radialCoefficientJet
        (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
        mode.1 radial)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous]
    with radius scaling representative
  rw [scaling, Pi.smul_apply, representative]

/-- Pointwise physical identification with the repaired same-point SC
conversion. This uses the actual Cartesian source reconstructed from all four
spin/scalar coordinates. -/
theorem physicalBulkSource_F0 (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (radius : ℝ) (bounded : |radius| ≤ 1)
    (axialAngle angle : ℝ) (source : SmoothQuotient parameters) :
    (actualAnnularBulkSource parameters L epsilon field radius bounded axialAngle
      (spinCartesianEquiv source)).F0 angle =
      polarTangentialComponent angle
        (sourceCoreValue (cartesianSourceVector source)
          (Grad.Constraints.polarClosedPoint radius bounded angle) axialAngle) := by
  rfl

theorem physicalBulkSource_F1 (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (radius : ℝ) (bounded : |radius| ≤ 1)
    (axialAngle angle : ℝ) (source : SmoothQuotient parameters) :
    (actualAnnularBulkSource parameters L epsilon field radius bounded axialAngle
      (spinCartesianEquiv source)).F1 angle =
      polarRadialComponent angle
        (sourceCoreValue (cartesianSourceVector source)
          (Grad.Constraints.polarClosedPoint radius bounded angle) axialAngle) := by
  rfl

theorem physicalBulkSource_F2 (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (radius : ℝ) (bounded : |radius| ≤ 1)
    (axialAngle angle : ℝ) (source : SmoothQuotient parameters) :
    (actualAnnularBulkSource parameters L epsilon field radius bounded axialAngle
      (spinCartesianEquiv source)).F2 angle =
      sourceCoreValue (source 3) (Grad.Constraints.polarClosedPoint radius bounded angle) axialAngle 0 /
        (L : ℂ) := by
  rfl

end Grad.SourceCollarBulk
