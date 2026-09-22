import AAR9SingleModeEnergyTesting
import AAR10ActualRadialPairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularEnergyPhase_single (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
        (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode (collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)
        (weightedCurveComplex 1 lower core.val.1)) := by
  classical
  apply lp.ext
  funext index
  rw [annularEnergyPhase_mode, annularEnergyValue_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, map_zero]

theorem annularEnergyRadial_single (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyRadial lower length positive
        (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode (collarScalar 1 lower (annularRadialCurve lower positive)
        (weightedCurveComplex 1 lower core.val.1)) := by
  classical
  apply lp.ext
  funext index
  rw [annularEnergyRadial_mode, annularEnergyValue_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, map_zero]

theorem annularEnergyD_single (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyD lower length positive
        (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode (annularDSymbol mode • weightedCurveComplex 1 lower core.val.1) := by
  classical
  apply lp.ext
  funext index
  rw [annularEnergyD_mode, annularEnergyValue_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, smul_zero]

theorem annularEnergyCell_single (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyCell lower length positive
        (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode (annularCellSymbol length mode • weightedCurveComplex 1 lower core.val.1) := by
  classical
  apply lp.ext
  funext index
  rw [annularEnergyCell_mode, annularEnergyValue_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, smul_zero]

theorem annularEnergyTrace_single (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (endpoint : Fin 2)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyTrace lower length positive bounded lengthPositive endpoint
        (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        core.val.1 (radialEndpointRadius lower endpoint)) := by
  classical
  rw [annularEnergyTrace_core]
  apply lp.ext
  funext index
  rw [finiteAnnularTraceCore_apply]
  simp only [Finsupp.single_apply, lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, Ne.symm same, if_false]
    exact smul_zero _

theorem annularBulk_single_inner (lower : ℝ) (mode : HighAnnularMode)
    (test : RadialL2 1 lower) (field : AnnularBulk lower) :
    inner ℂ (lp.single 2 mode test : AnnularBulk lower) field = inner ℂ test (field mode) :=
  lp.inner_single_left (𝕜 := ℂ) (G := fun _ : HighAnnularMode => RadialL2 1 lower) mode test field

section Formula
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The literal conjugated single-mode energy formula, retaining the outer
Robin contribution. No differential equation is assumed. -/
theorem annularForm_single (mode : HighAnnularMode) (core : complexSmoothRadialCore 1)
    (field : annularEnergySpace lower length positive) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field
      (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      inner ℂ (weightedCurveComplex 1 lower core.val.2 +
        collarScalar 1 lower (annularPhaseCurve parameters mode.val.2) (weightedCurveComplex 1 lower core.val.1))
        (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode) +
      inner ℂ (weightedCurveComplex 1 lower
        (continuousCurveWeight 1 (annularPotentialWeight lower length positive mode.val.1 mode.val.2) core.val.1))
        (annularEnergyMass lower length positive field mode) +
      inner ℂ ((Real.sqrt 2 : ℂ) • core.val.1 1)
        (annularEnergyOuter lower length positive field mode) := by
  classical
  let test := annularEnergyCoreInto lower length positive (Finsupp.single mode core)
  let derivative := annularEnergyDerivative lower length positive field
  let phase := annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field
  let testSlope := weightedCurveComplex 1 lower core.val.2
  let testPhase := collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)
    (weightedCurveComplex 1 lower core.val.1)
  have phaseLaw := annularEnergyPhase_single parameters lower length positive lengthPositive widthHalf widthLength mode core
  have derivativeLaw := annularEnergyDerivative_single lower length positive mode core
  have second : inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test) derivative =
      inner ℂ testPhase (derivative mode) :=
    (congrArg (fun value : AnnularBulk lower => inner ℂ value derivative) phaseLaw).trans
      (annularBulk_single_inner lower mode testPhase derivative)
  have third : inner ℂ (annularEnergyDerivative lower length positive test) phase =
      inner ℂ testSlope (phase mode) :=
    (congrArg (fun value : AnnularBulk lower => inner ℂ value phase) derivativeLaw).trans
      (annularBulk_single_inner lower mode testSlope phase)
  have fourth : inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test) phase =
      inner ℂ testPhase (phase mode) :=
    (congrArg (fun value : AnnularBulk lower => inner ℂ value phase) phaseLaw).trans
      (annularBulk_single_inner lower mode testPhase phase)
  have combined := congrArg₂ (fun first second : ℂ => first - second)
    (congrArg₂ (fun first second : ℂ => first - second)
      (congrArg₂ (fun first second : ℂ => first + second)
        (annularEnergy_single_inner lower length positive mode core field) second) third) fourth
  refine combined.trans ?_
  change _ = inner ℂ (testSlope + testPhase) (derivative mode - phase mode) + _ + _
  rw [inner_add_left, inner_sub_right, inner_sub_right]
  abel

theorem annularFunctional_single (bounded : lower < 1) (mode : HighAnnularMode)
    (core : complexSmoothRadialCore 1) (source : AnnularForcing lower) :
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source
      (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      inner ℂ (weightedCurveComplex 1 lower core.val.2 +
        collarScalar 1 lower (annularPhaseCurve parameters mode.val.2) (weightedCurveComplex 1 lower core.val.1) +
        collarScalar 1 lower (annularRadialCurve lower positive) (weightedCurveComplex 1 lower core.val.1)) (source.1 mode) -
      inner ℂ (annularDSymbol mode • weightedCurveComplex 1 lower core.val.1) (source.2.1 mode) -
      inner ℂ (annularCellSymbol length mode • weightedCurveComplex 1 lower core.val.1) (source.2.2.1 mode) -
      inner ℂ ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • core.val.1 1) (source.2.2.2 mode) := by
  classical
  let test := annularEnergyCoreInto lower length positive (Finsupp.single mode core)
  let slope := annularEnergyDerivative lower length positive test
  let phase := annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test
  let radial := annularEnergyRadial lower length positive test
  have slopePair := (congrArg (fun value : AnnularBulk lower => inner ℂ value source.1)
    (annularEnergyDerivative_single lower length positive mode core)).trans
    (annularBulk_single_inner lower mode _ source.1)
  have phasePair := (congrArg (fun value : AnnularBulk lower => inner ℂ value source.1)
    (annularEnergyPhase_single parameters lower length positive lengthPositive widthHalf widthLength mode core)).trans
    (annularBulk_single_inner lower mode _ source.1)
  have radialPair := (congrArg (fun value : AnnularBulk lower => inner ℂ value source.1)
    (annularEnergyRadial_single lower length positive mode core)).trans
    (annularBulk_single_inner lower mode _ source.1)
  have first := (inner_add_left (𝕜 := ℂ) (slope + phase) radial source.1).trans
    (congrArg₂ (fun first second : ℂ => first + second)
      ((inner_add_left (𝕜 := ℂ) slope phase source.1).trans
        (congrArg₂ (fun first second : ℂ => first + second) slopePair phasePair)) radialPair)
  have second := (congrArg (fun value : AnnularBulk lower => inner ℂ value source.2.1)
    (annularEnergyD_single lower length positive mode core)).trans
    (annularBulk_single_inner lower mode _ source.2.1)
  have third := (congrArg (fun value : AnnularBulk lower => inner ℂ value source.2.2.1)
    (annularEnergyCell_single lower length positive mode core)).trans
    (annularBulk_single_inner lower mode _ source.2.2.1)
  have fourth := (congrArg (fun value : AnnularBoundary => inner ℂ value source.2.2.2)
    (annularEnergyTrace_single lower length positive bounded lengthPositive 1 mode core)).trans
    (lp.inner_single_left (𝕜 := ℂ) (G := fun _ : HighAnnularMode => ComplexEuclidean 1)
      mode _ source.2.2.2)
  have combined := congrArg₂ (fun first second : ℂ => first - second)
    (congrArg₂ (fun first second : ℂ => first - second)
      (congrArg₂ (fun first second : ℂ => first - second) first second) third) fourth
  refine combined.trans ?_
  rw [inner_add_left, inner_add_left]
  rfl

end Formula
end Grad.AnnularReconstruction
