import AEE1ActualContinuousRadialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Literal one-component complex Fourier value used by the ADY bulk. -/
def scalarOne : ℂ →L[ℂ] ComplexEuclidean 1 :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))

theorem scalarOne_apply_zero (value : ℂ) : scalarOne value 0 = value := by
  simp [scalarOne]

theorem scalarOne_norm (value : ℂ) : ‖scalarOne value‖ = ‖value‖ := by
  have square : ‖scalarOne value‖ ^ 2 = ‖value‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_one, scalarOne_apply_zero]
  nlinarith [norm_nonneg (scalarOne value), norm_nonneg value]

theorem scalarOne_surjective : Function.Surjective scalarOne := by
  intro value
  refine ⟨value 0, ?_⟩
  apply PiLp.ext
  intro index
  fin_cases index
  exact scalarOne_apply_zero _

def scalarOneCurve (curve : C(ℝ, ℂ)) : C(ℝ, ComplexEuclidean 1) :=
  ⟨fun radius => scalarOne (curve radius), scalarOne.continuous.comp curve.continuous⟩

def scalarRadialRealization (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (initial : ℂ) (derivative : C(ℝ, ℂ)) : WeightedRadialH1 1 lower :=
  continuousRadialRealization 1 lower positive bounded (scalarOne initial) (scalarOneCurve derivative)

theorem scalarRadialRealization_actual (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value : ℝ → ℂ) (derivative : C(ℝ, ℂ))
    (continuousValue : ContinuousOn value (Icc lower 1))
    (differentiates : ∀ radius ∈ Ioo lower 1, HasDerivAt value (derivative radius) radius)
    (radius : Icc lower 1) :
    weightedRadialSection 1 lower positive bounded
      (scalarRadialRealization lower positive bounded (value lower) derivative) radius = scalarOne (value radius.val) := by
  apply continuousRadialRealization_actual 1 lower positive bounded (fun point => scalarOne (value point))
    (scalarOneCurve derivative) (scalarOne.continuous.comp_continuousOn continuousValue)
  intro point member
  exact (scalarOne.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt point (differentiates point member)

theorem scalarRadialRealization_slope (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (initial : ℂ) (derivative : C(ℝ, ℂ)) :
    collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le
        (scalarRadialRealization lower positive bounded initial derivative)) =
      collarContinuousL2 (ComplexEuclidean 1) lower (scalarOneCurve derivative) :=
  continuousRadialRealization_slope 1 lower positive bounded (scalarOne initial) (scalarOneCurve derivative)

theorem scalarRadialRealization_incoming (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (initial : ℂ) (derivative : C(ℝ, ℂ)) :
    weightedRadialTrace 1 lower positive bounded 0
      (scalarRadialRealization lower positive bounded initial derivative) = scalarOne initial :=
  continuousRadialRealization_incoming 1 lower positive bounded (scalarOne initial) (scalarOneCurve derivative)

end Grad.AnnularLowCompletion
