import AIA11LiteralDecodedCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighWeak Grad.CircularHighRegularity

/-- A pointwise quadratic identity becomes the actual completed L2 pairing identity. -/
theorem collarScalar_quadratic_inner (lower : ℝ) (first second : C(ℝ, ℝ)) (a c : ℝ)
    (relation : ∀ radius ∈ Icc lower 1, first radius ^ 2 = a * second radius ^ 2 + c)
    (test field : RadialL2 1 lower) :
    inner ℂ (collarScalar 1 lower first test) (collarScalar 1 lower first field) =
      (a : ℂ) * inner ℂ (collarScalar 1 lower second test) (collarScalar 1 lower second field) +
      (c : ℂ) * inner ℂ test field := by
  have operatorIdentity : collarScalar 1 lower first (collarScalar 1 lower first field) =
      (a : ℂ) • collarScalar 1 lower second (collarScalar 1 lower second field) + (c : ℂ) • field := by
    apply Lp.ext
    filter_upwards [collarScalar_ae 1 lower first (collarScalar 1 lower first field),
      collarScalar_ae 1 lower first field,
      collarScalar_ae 1 lower second (collarScalar 1 lower second field),
      collarScalar_ae 1 lower second field,
      Lp.coeFn_add ((a : ℂ) • collarScalar 1 lower second (collarScalar 1 lower second field)) ((c : ℂ) • field),
      Lp.coeFn_smul (a : ℂ) (collarScalar 1 lower second (collarScalar 1 lower second field)),
      Lp.coeFn_smul (c : ℂ) field, ae_restrict_mem measurableSet_Icc]
      with radius firstOuter firstInner secondOuter secondInner sumLaw aLaw cLaw inside
    simp only [Pi.add_apply, Pi.smul_apply] at sumLaw aLaw cLaw
    rw [firstOuter, firstInner, sumLaw, aLaw, secondOuter, secondInner, cLaw]
    apply PiLp.ext
    intro coordinate
    change ((first radius : ℂ) * ((first radius : ℂ) * (field radius).ofLp coordinate)) =
      (a : ℂ) * ((second radius : ℂ) * ((second radius : ℂ) * (field radius).ofLp coordinate)) + (c : ℂ) * (field radius).ofLp coordinate
    have scalar : (first radius : ℂ) ^ 2 = (a : ℂ) * (second radius : ℂ) ^ 2 + (c : ℂ) := by
      exact_mod_cast relation radius inside
    linear_combination scalar * (field radius).ofLp coordinate
  rw [collarScalar_inner, operatorIdentity, inner_add_right, inner_smul_right, inner_smul_right,
    collarScalar_inner]

/-- The exact mode potential pairing, with the original m and n/L factors. -/
theorem annularEnergyMass_pairing_mode (lower L : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (test field : annularEnergySpace lower L positive) :
    inner ℂ (annularEnergyMass lower L positive test mode) (annularEnergyMass lower L positive field mode) =
      ((mode.val.1 : ℂ) ^ 2) * inner ℂ (highEnergyRadius lower L positive test mode) (highEnergyRadius lower L positive field mode) +
      ((highMultiplier mode.val.1 * ((mode.val.2 : ℝ) / L) ^ 2 : ℝ) : ℂ) *
        inner ℂ (annularEnergyValue lower L positive test mode) (annularEnergyValue lower L positive field mode) := by
  rw [annularEnergyMass_mode, annularEnergyMass_mode, highEnergyRadius_mode, highEnergyRadius_mode]
  convert collarScalar_quadratic_inner lower (annularPotentialWeight lower L positive mode.val.1 mode.val.2)
    (highReciprocalRadius lower positive) ((mode.val.1 : ℝ) ^ 2)
    (highMultiplier mode.val.1 * ((mode.val.2 : ℝ) / L) ^ 2) ?_
    (annularEnergyValue lower L positive test mode) (annularEnergyValue lower L positive field mode) using 1
  · norm_cast
  intro radius inside
  rw [annularPotentialWeight_sq lower L positive mode.val.1 mode.val.2 radius inside.1]
  change (mode.val.1 : ℝ) ^ 2 / radius ^ 2 + highMultiplier mode.val.1 * (mode.val.2 : ℝ) ^ 2 / L ^ 2 =
    (mode.val.1 : ℝ) ^ 2 * (max lower radius)⁻¹ ^ 2 + highMultiplier mode.val.1 * ((mode.val.2 : ℝ) / L) ^ 2
  rw [max_eq_right inside.1]
  ring

/-- The phase and reciprocal radius cross terms cancel without any extra regularity assumption. -/
theorem phase_radius_pairing (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (mode : HighAnnularMode) (test field : annularEnergySpace lower L positive) :
    inner ℂ (annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength test mode)
        (highEnergyRadius lower L positive field mode) =
      inner ℂ (highEnergyRadius lower L positive test mode)
        (annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field mode) := by
  rw [annularTiltEnergyPhase_mode, annularTiltEnergyPhase_mode, highEnergyRadius_mode, highEnergyRadius_mode,
    collarScalar_inner, collarScalar_inner, collarScalar_comm]

end Grad.AnnularCircularForm
