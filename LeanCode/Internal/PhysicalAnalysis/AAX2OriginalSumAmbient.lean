import AAX1OriginalAngularCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFourSource
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularFluxTrace

abbrev AnnularFourTail3 (lower : ℝ) := WithLp 1 (AnnularBulk lower × AnnularBulk lower)
abbrev AnnularFourTail2 (lower : ℝ) := WithLp 1 (AnnularBulk lower × AnnularFourTail3 lower)
abbrev AnnularFourTail1 (lower length : ℝ) (positive : 0 < lower) :=
  WithLp 1 (annularEnergySpace lower length positive × AnnularFourTail2 lower)

/-- AG30 with its fourth residual: literal five-component SUM norm.
The first, third and fifth coordinates have one extra angular order. -/
abbrev AnnularFourAmbient (lower length : ℝ) (positive : 0 < lower) :=
  WithLp 1 (AnnularBulk lower × AnnularFourTail1 lower length positive)

private def sumFirst {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] : WithLp 1 (E × F) →L[ℂ] E :=
  (ContinuousLinearMap.fst ℂ E F).comp (WithLp.prodContinuousLinearEquiv 1 ℂ E F).toContinuousLinearMap

private def sumSecond {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] : WithLp 1 (E × F) →L[ℂ] F :=
  (ContinuousLinearMap.snd ℂ E F).comp (WithLp.prodContinuousLinearEquiv 1 ℂ E F).toContinuousLinearMap

private theorem sumNorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 1 (E × F)) : ‖data‖ = ‖data.fst‖ + ‖data.snd‖ := by
  simpa using WithLp.prod_norm_eq_add (p := 1) (by norm_num) data

section Coordinates
variable (lower length : ℝ) (positive : 0 < lower)

private def tail1 : AnnularFourAmbient lower length positive →L[ℂ] AnnularFourTail1 lower length positive :=
  sumSecond (E := AnnularBulk lower) (F := AnnularFourTail1 lower length positive)

private def tail2 : AnnularFourAmbient lower length positive →L[ℂ] AnnularFourTail2 lower :=
  (sumSecond (E := annularEnergySpace lower length positive) (F := AnnularFourTail2 lower)).comp
    (tail1 lower length positive)

private def tail3 : AnnularFourAmbient lower length positive →L[ℂ] AnnularFourTail3 lower :=
  (sumSecond (E := AnnularBulk lower) (F := AnnularFourTail3 lower)).comp (tail2 lower length positive)

def annularFourP : AnnularFourAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  sumFirst (E := AnnularBulk lower) (F := AnnularFourTail1 lower length positive)

def annularFourW : AnnularFourAmbient lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  (sumFirst (E := annularEnergySpace lower length positive) (F := AnnularFourTail2 lower)).comp
    (tail1 lower length positive)

def annularFourF0 : AnnularFourAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (sumFirst (E := AnnularBulk lower) (F := AnnularFourTail3 lower)).comp (tail2 lower length positive)

def annularFourF2 : AnnularFourAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (sumFirst (E := AnnularBulk lower) (F := AnnularBulk lower)).comp (tail3 lower length positive)

def annularFourG : AnnularFourAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (sumSecond (E := AnnularBulk lower) (F := AnnularBulk lower)).comp (tail3 lower length positive)

theorem annularFourAmbient_norm (data : AnnularFourAmbient lower length positive) :
    ‖data‖ = ‖annularFourP lower length positive data‖ + ‖annularFourW lower length positive data‖ +
      ‖annularFourF0 lower length positive data‖ + ‖annularFourF2 lower length positive data‖ +
      ‖annularFourG lower length positive data‖ := by
  change ‖data‖ = ‖data.fst‖ + ‖data.snd.fst‖ + ‖data.snd.snd.fst‖ +
    ‖data.snd.snd.snd.fst‖ + ‖data.snd.snd.snd.snd‖
  rw [sumNorm data, sumNorm data.snd, sumNorm data.snd.snd, sumNorm data.snd.snd.snd]
  ring

end Coordinates
end Grad.AnnularFourSource
