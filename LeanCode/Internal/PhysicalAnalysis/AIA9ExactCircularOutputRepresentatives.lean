import AIA8ActualCompletedCircularCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.GaugeCoefficients.Physical.Ledger

theorem highThreePacket_ae (lower : ℝ) (first second third : AnnularBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      (highBulkSlot lower (0 : Fin 3) first + highBulkSlot lower (1 : Fin 3) second + highBulkSlot lower (2 : Fin 3) third)
        mode.val radius = WithLp.toLp 2 ![first mode radius 0, second mode radius 0, third mode radius 0] := by
  rw [ae_all_iff]
  intro mode
  filter_upwards [highBulkSlot_ae lower (0 : Fin 3) first, highBulkSlot_ae lower (1 : Fin 3) second,
    highBulkSlot_ae lower (2 : Fin 3) third,
    Lp.coeFn_add (highBulkSlot lower (0 : Fin 3) first mode.val) (highBulkSlot lower (1 : Fin 3) second mode.val),
    Lp.coeFn_add (highBulkSlot lower (0 : Fin 3) first mode.val + highBulkSlot lower (1 : Fin 3) second mode.val)
      (highBulkSlot lower (2 : Fin 3) third mode.val)] with radius one two three sum12 sum123
  change ((highBulkSlot lower (0 : Fin 3) first mode.val + highBulkSlot lower (1 : Fin 3) second mode.val) +
    highBulkSlot lower (2 : Fin 3) third mode.val) radius = _
  simp only [Pi.add_apply] at sum12 sum123
  rw [sum123, sum12, one mode, two mode, three mode]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [operatorBasis]

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- The bounded scalar output coordinates have exactly the same literal radial representatives. -/
theorem circularHighCoordinates_ae (field : annularEnergySpace lower L positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      circularHighX parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0 =
        -retainedBInverseMultiplier mode.val *
          (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0 +
            2 * highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode radius 0) ∧
      circularHighC lower L positive field mode radius 0 =
        -highEnergyCell lower L positive (bEnergyDecode lower L positive field) mode radius 0 ∧
      circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0 =
        -highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) mode radius 0 -
          2 * angularInverseMultiplier mode.val *
            circularHighX parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0 := by
  rw [ae_all_iff]
  intro mode
  let d := highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode
  let r := highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode
  let c := highEnergyCell lower L positive (bEnergyDecode lower L positive field) mode
  let a := highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) mode
  let x := circularHighX parameters lower L positive lengthPositive widthHalf widthLength field mode
  have xEquality : x = (-retainedBInverseMultiplier mode.val) • (d + (2 : ℂ) • r) :=
    circularHighX_mode parameters lower L positive lengthPositive widthHalf widthLength field mode
  filter_upwards [Lp.coeFn_smul (-retainedBInverseMultiplier mode.val) (d + (2 : ℂ) • r),
    Lp.coeFn_add d ((2 : ℂ) • r), Lp.coeFn_smul (2 : ℂ) r, Lp.coeFn_neg c,
    Lp.coeFn_sub (-a) ((2 : ℂ) • (angularInverseMultiplier mode.val • x)),
    Lp.coeFn_neg a, Lp.coeFn_smul (2 : ℂ) (angularInverseMultiplier mode.val • x),
    Lp.coeFn_smul (angularInverseMultiplier mode.val) x]
    with radius xLaw sumLaw rLaw cLaw rvLaw aLaw twoLaw kLaw
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at xLaw sumLaw rLaw cLaw rvLaw aLaw twoLaw kLaw
  have first : x radius 0 = -retainedBInverseMultiplier mode.val * (d radius 0 + 2 * r radius 0) := by
    rw [xEquality, xLaw, sumLaw, rLaw]
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  have second : circularHighC lower L positive field mode radius 0 = -c radius 0 := by
    rw [circularHighC_mode, cLaw]
    rfl
  have third : circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field mode radius 0 =
      -a radius 0 - 2 * angularInverseMultiplier mode.val * x radius 0 := by
    rw [circularHighRV_mode, rvLaw, aLaw, twoLaw, kLaw]
    simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  exact ⟨first, second, third⟩

end Grad.AnnularCircularForm
