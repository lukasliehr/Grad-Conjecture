import AKI40RepresentedCoreExactGraphClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularOriginalSmoothCore Grad.AnnularPhysicalFourier Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

/-- Genuine radial jets of the SAME phase-conjugated original tuple field. -/
def tupleConjugatedJetSection (order : ℕ) (mode : ℤ × ℤ) : RadialContinuousSection 1 lower :=
  hilbertRadialJetSection lower bounded (tupleWeightedCurve parameters lower tuple slot)
    (tupleWeightedCurve_smooth parameters lower tuple slot) order 0 mode

theorem tupleConjugatedJetSection_derivative (order : ℕ) (mode : ℤ × ℤ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (tupleConjugatedJetSection parameters lower bounded tuple slot order mode))
      (radialSectionExtension 1 lower bounded.le
        (tupleConjugatedJetSection parameters lower bounded tuple slot (order+1) mode) radius)
      (Icc lower 1) radius := by
  have actual := hilbertRadialJetSection_derivative lower bounded (tupleWeightedCurve parameters lower tuple slot)
    (tupleWeightedCurve_smooth parameters lower tuple slot) order 0 mode radius inside
  have same (location : ℝ) (member : location ∈ Icc lower 1) :
      radialSectionExtension 1 lower bounded.le (tupleConjugatedJetSection parameters lower bounded tuple slot order mode) location =
        iteratedDerivWithin order (tupleWeightedCurve parameters lower tuple slot 0) (Icc lower 1) location mode := by
    change (tupleConjugatedJetSection parameters lower bounded tuple slot order mode) (radialClamp lower bounded.le location) = _
    rw [radialClamp_eq lower bounded.le location member]
    rfl
  have slope : radialSectionExtension 1 lower bounded.le
      (tupleConjugatedJetSection parameters lower bounded tuple slot (order+1) mode) radius =
      hilbertRadialJetSection lower bounded (tupleWeightedCurve parameters lower tuple slot)
        (tupleWeightedCurve_smooth parameters lower tuple slot) (order+1) 0 mode ⟨radius,inside⟩ := by
    change (tupleConjugatedJetSection parameters lower bounded tuple slot (order+1) mode) (radialClamp lower bounded.le radius) = _
    rw [radialClamp_eq lower bounded.le radius inside]
    rfl
  rw [slope]
  exact actual.congr same (same radius inside)

def tupleConjugatedJetL2 (order : ℕ) (mode : ℤ × ℤ) : CollarL2 (ComplexEuclidean 1) lower :=
  radialSectionL2 1 lower positive bounded.le (tupleConjugatedJetSection parameters lower bounded tuple slot order mode)

theorem tupleConjugatedJet_weak (order : ℕ) (mode : ℤ × ℤ) :
    CollarWeakDerivative lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot order mode)
      (tupleConjugatedJetL2 parameters lower positive bounded tuple slot (order+1) mode) :=
  collarWeakDerivative_of_closedClassical lower bounded.le _ _
    (tupleConjugatedJetSection_derivative parameters lower bounded tuple slot order mode)

/-- Actual original weighted H1 completion of each radial Fourier mode.
Both stored coordinates are determined by the SAME smooth field. -/
def tupleConjugatedRadialGraph (mode : ℤ × ℤ) : WeightedRadialH1 1 lower :=
  weakRadialRealization 1 lower positive bounded
    (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode)
    (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 1 mode)
    (tupleConjugatedJet_weak parameters lower positive bounded tuple slot 0 mode)

theorem tupleConjugatedRadialGraph_coordinate (mode : ℤ × ℤ) (coordinate : Fin 2) :
    weightedRadialCoordinate 1 lower coordinate (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode) =
      radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot coordinate.val mode) := by
  rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le]
  fin_cases coordinate
  · exact congrArg (radialSqrtMap 1 lower) (weakRadialRealization_value 1 lower positive bounded _ _ _)
  · exact congrArg (radialSqrtMap 1 lower) (weakRadialRealization_slope 1 lower positive bounded _ _ _)

theorem tupleConjugatedRadialGraph_bound (mode : ℤ × ℤ) :
    ‖tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode‖ ≤
      ‖radialSqrtMap 1 lower‖ *
        (‖tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode‖ +
          ‖tupleConjugatedJetSection parameters lower bounded tuple slot 1 mode‖) := by
  let graph := tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode
  have square := weightedRadialH1_norm_sq 1 lower graph
  have sumBound : ‖graph‖ ≤ ‖weightedRadialCoordinate 1 lower 0 graph‖ + ‖weightedRadialCoordinate 1 lower 1 graph‖ := by
    nlinarith [norm_nonneg graph,norm_nonneg (weightedRadialCoordinate 1 lower 0 graph),
      norm_nonneg (weightedRadialCoordinate 1 lower 1 graph),
      mul_nonneg (norm_nonneg (weightedRadialCoordinate 1 lower 0 graph)) (norm_nonneg (weightedRadialCoordinate 1 lower 1 graph))]
  have coordinateBound (coordinate : Fin 2) : ‖weightedRadialCoordinate 1 lower coordinate graph‖ ≤
      ‖radialSqrtMap 1 lower‖ * ‖tupleConjugatedJetSection parameters lower bounded tuple slot coordinate.val mode‖ := by
    rw [tupleConjugatedRadialGraph_coordinate]
    apply ((radialSqrtMap 1 lower).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (radialSectionL2Linear_bound 1 lower positive bounded.le _).trans_eq (one_mul _)
  exact sumBound.trans ((add_le_add (coordinateBound 0) (coordinateBound 1)).trans_eq (mul_add _ _ _).symm)

end Grad.AnnularOriginalCoreRealization
