import AIA10CompletedCircularPacketIdentity
import AIA15ActualCircularModePairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- Exact completed circle pairing before radial integration: both endpoint contributions remain present in the cross term. -/
theorem circularHighBulkFormValue_radial (power : ℕ) (field test : annularEnergySpace lower L positive) :
    circularHighBulkFormValue parameters L lower positive bounded lengthPositive widthHalf widthLength power field test =
      inner ℂ (annularEnergyDerivative lower L positive test +
        annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength test)
        (annularEnergyDerivative lower L positive field -
          annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field) +
      2 * (inner ℂ (annularEnergyDerivative lower L positive test) (highEnergyRadius lower L positive field) +
        inner ℂ (highEnergyRadius lower L positive test) (annularEnergyDerivative lower L positive field)) +
      inner ℂ (annularEnergyMass lower L positive test) (annularEnergyMass lower L positive field) := by
  rw [circularHighBulkFormValue_coordinates]
  let tx := highPhysicalTestDerivative parameters lower L positive lengthPositive widthHalf widthLength test
  let tc := highEnergyCell lower L positive (bEnergyDecode lower L positive test)
  let ta := highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive test)
  let fx := circularHighX parameters lower L positive lengthPositive widthHalf widthLength field
  let fc := circularHighC lower L positive field
  let fa := circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field
  let dt := annularEnergyDerivative lower L positive test
  let df := annularEnergyDerivative lower L positive field
  let pt := annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength test
  let pf := annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field
  let rt := highEnergyRadius lower L positive test
  let rf := highEnergyRadius lower L positive field
  let mt := annularEnergyMass lower L positive test
  let mf := annularEnergyMass lower L positive field
  have sx := lp.summable_inner (𝕜 := ℂ) tx fx
  have sc := lp.summable_inner (𝕜 := ℂ) tc fc
  have sa := lp.summable_inner (𝕜 := ℂ) ta fa
  have sd := lp.summable_inner (𝕜 := ℂ) (dt + pt) (df - pf)
  have sr1 := lp.summable_inner (𝕜 := ℂ) dt rf
  have sr2 := lp.summable_inner (𝕜 := ℂ) rt df
  have sm := lp.summable_inner (𝕜 := ℂ) mt mf
  change -(inner ℂ tx fx + inner ℂ tc fc + inner ℂ ta fa) =
    inner ℂ (dt + pt) (df - pf) + 2 * (inner ℂ dt rf + inner ℂ rt df) + inner ℂ mt mf
  simp only [lp.inner_eq_tsum]
  rw [← sx.tsum_add sc, ← (sx.add sc).tsum_add sa, ← tsum_neg,
    ← sr1.tsum_add sr2, ← tsum_mul_left, ← sd.tsum_add ((sr1.add sr2).mul_left (2 : ℂ)),
    ← (sd.add ((sr1.add sr2).mul_left (2 : ℂ))).tsum_add sm]
  apply tsum_congr
  intro mode
  exact circularPhysical_pairing_mode parameters lower L positive lengthPositive widthHalf widthLength mode field test

end Grad.AnnularCircularForm
