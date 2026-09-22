import AAR19PhysicalSecondRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.CircularHighWeak Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularMode_real_ne_zero (mode : HighAnnularMode) : (mode.val.1 : ℝ) ≠ 0 := by
  have high : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  intro zero
  rw [zero, abs_zero] at high
  linarith

def annularSecondRealCurve (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => (mode.val.1 : ℝ) / (max lower radius) ^ 2 +
      (mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2),
    (continuous_const.div ((continuous_const.max continuous_id).pow 2)
      (fun radius => pow_ne_zero 2 (positive.trans_le (le_max_left lower radius)).ne')).add continuous_const⟩

theorem annularSecondPotential_real (length radius : ℝ) (lengthPositive : 0 < length)
    (radiusPositive : 0 < radius) (mode : HighAnnularMode) :
    annularPotential length radius mode.val.1 mode.val.2 - 4 / radius ^ 2 =
      ((mode.val.1 : ℝ) * highMultiplier mode.val.1) *
        ((mode.val.1 : ℝ) / radius ^ 2 + (mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2)) := by
  rw [annularPotential, highMultiplier_high _ (Grad.ActualReferenceAssembly.highMode_not_low _ mode.property)]
  field_simp [annularMode_real_ne_zero mode, lengthPositive.ne', radiusPositive.ne']
  ring

theorem annularSecondPotential_symbol (length radius : ℝ) (lengthPositive : 0 < length)
    (radiusPositive : 0 < radius) (mode : HighAnnularMode) :
    ((annularPotential length radius mode.val.1 mode.val.2 - 4 / radius ^ 2 : ℝ) : ℂ) =
      annularDSymbol mode * (-Complex.I *
        (((mode.val.1 : ℝ) / radius ^ 2 + (mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2) : ℝ) : ℂ)) := by
  rw [annularSecondPotential_real length radius lengthPositive radiusPositive mode, annularDSymbol]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem annularSecondSource_symbol (length : ℝ) (lengthPositive : 0 < length) (mode : HighAnnularMode) :
    annularDSymbol mode * (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ) =
      annularCellSymbol length mode := by
  have realIdentity : ((mode.val.1 : ℝ) * highMultiplier mode.val.1) *
      ((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length)) = highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length := by
    field_simp [annularMode_real_ne_zero mode, lengthPositive.ne']
  change (Complex.I * (((mode.val.1 : ℝ) * highMultiplier mode.val.1 : ℝ) : ℂ)) *
    (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ) =
    Complex.I * ((highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length : ℝ) : ℂ)
  rw [mul_assoc, ← Complex.ofReal_mul, realIdentity]

theorem annularSecond_pointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b c : ℝ) (d : ℂ) (x : E)
    (identity : ((a - 4 * (b * b) : ℝ) : ℂ) = d * (-Complex.I * (c : ℂ))) :
    a • x - (4 : ℝ) • (b • (b • x)) = d • (-Complex.I • (c • x)) := by
  rw [smul_smul b, smul_smul (4 : ℝ), ← sub_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (congrArg (fun scalar : ℂ => scalar • x) identity).trans (by rw [mul_smul, mul_smul]; rfl)

theorem annularScalar_second_operator (lower : ℝ) (potential inverse coefficient : C(ℝ, ℝ))
    (symbol : ℂ) (field : CollarL2 (ComplexEuclidean 1) lower)
    (scalar : ∀ radius ∈ Icc lower (1 : ℝ),
      ((potential radius - 4 * (inverse radius * inverse radius) : ℝ) : ℂ) =
        symbol * (-Complex.I * (coefficient radius : ℂ))) :
    collarScalar 1 lower potential field -
      (4 : ℝ) • collarScalar 1 lower inverse (collarScalar 1 lower inverse field) =
      symbol • (-Complex.I • collarScalar 1 lower coefficient field) := by
  apply Lp.ext
  filter_upwards [
    collarScalar_ae 1 lower potential field,
    collarScalar_ae 1 lower inverse (collarScalar 1 lower inverse field),
    collarScalar_ae 1 lower inverse field,
    collarScalar_ae 1 lower coefficient field,
    Lp.coeFn_sub (collarScalar 1 lower potential field)
      ((4 : ℝ) • collarScalar 1 lower inverse (collarScalar 1 lower inverse field)),
    Lp.coeFn_smul (4 : ℝ) (collarScalar 1 lower inverse (collarScalar 1 lower inverse field)),
    Lp.coeFn_smul symbol (-Complex.I • collarScalar 1 lower coefficient field),
    Lp.coeFn_smul (-Complex.I) (collarScalar 1 lower coefficient field),
    ae_restrict_mem measurableSet_Icc]
    with radius potentialLaw radial1 radial2 coefficientLaw difference scaled outer inner inside
  rw [difference, Pi.sub_apply, scaled, Pi.smul_apply, potentialLaw, radial1, radial2,
    outer, Pi.smul_apply, inner, Pi.smul_apply, coefficientLaw]
  exact annularSecond_pointwise (potential radius) (inverse radius) (coefficient radius)
    symbol (field radius) (scalar radius inside)

/-- The literal original second-row coefficient on ordinary radial L2. -/
theorem annularSecondPotential_operator (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (mode : HighAnnularMode) (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularPotentialCurve lower length positive mode) field -
      (4 : ℝ) • collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (collarScalar 1 lower (annularInverseRadiusCurve lower positive) field) =
      annularDSymbol mode • (-Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode) field) := by
  apply annularScalar_second_operator
  intro radius inside
  rw [annularPotentialCurve_literal lower length positive mode radius inside.1]
  change ((annularPotential length radius mode.val.1 mode.val.2 -
    (4 : ℝ) * ((1 / max lower radius) * (1 / max lower radius)) : ℝ) : ℂ) =
      annularDSymbol mode * (-Complex.I *
        (((mode.val.1 : ℝ) / (max lower radius) ^ 2 + (mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2) : ℝ) : ℂ))
  rw [max_eq_right inside.1]
  have realProduct : (4 : ℝ) * ((1 / radius) * (1 / radius)) = 4 / radius ^ 2 := by ring
  rw [realProduct]
  exact annularSecondPotential_symbol length radius lengthPositive (positive.trans_le inside.1) mode

end Grad.AnnularReconstruction
