import AKCK5ActualPrimitiveSourceEnergy
import AKCD4TwoNativeEnergyInputs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarRestriction Grad.SourceCollarFullSource
open Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra Grad.AnnularSmoothCore
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.AnnularWeightedSmoothness Grad.AnnularStrongData

/-- The same primitive source at grade zero is paid independently of all
high source grades and high coefficient budgets. -/
theorem actualPrimitiveCurve_baseEnergy (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) :
    ∃ constants : Fin 4 → ℝ, (∀ slot, 0 ≤ constants slot) ∧
    ∀ source : SmoothQuotient parameters, ∀ slot : Fin 4,
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖actualCartesianPrimitiveCurve parameters length lower positive bounded source slot 0 radius‖^2)) ≤
      ENNReal.ofReal ((constants slot * ‖quotientEta parameters 4 source‖)^2) := by
  obtain ⟨constants,nonnegative,energy⟩ := actualPrimitiveCurve_fourEnergy parameters length lower positive bounded 0
  refine ⟨constants,nonnegative,?_⟩
  intro source slot
  apply (lintegral_mono_ae ?_).trans (energy source slot)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  have same := (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).shift bounded 0 1 radius inside
  have lowered := hilbertReserve_same parameters 1 1
    (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot 1 radius)
    (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot 0 radius) same
  have bound := (hilbertReserve parameters 1 1).le_opNorm
    (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot 1 radius)
  rw [lowered] at bound
  have normBound := bound.trans ((mul_le_mul_of_nonneg_right (hilbertReserve_norm_le parameters 1 1)
    (norm_nonneg _)).trans_eq (one_mul _))
  exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr normBound)

/-- Combining the three literal inserted source slots uses only their own
energies; the constant is independent of coefficients and source. -/
theorem sameKnownSeven_energy (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters)
    (grade : ℕ) (payments : Fin 4 → ℝ) (nonnegative : ∀ slot, 0 ≤ payments slot)
    (energy : ∀ slot : Fin 4,
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖actualCartesianPrimitiveCurve parameters length lower positive bounded source slot grade radius‖^2)) ≤
      ENNReal.ofReal ((payments slot)^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖actualCartesianKnownSevenCurve parameters length lower positive bounded source grade radius‖^2)) ≤
    ENNReal.ofReal ((4*(‖hilbertSlotInjection parameters 4‖*payments 0 +
      ‖hilbertSlotInjection parameters 5‖*payments 1 + ‖hilbertSlotInjection parameters 6‖*payments 2))^2) := by
  have p0 := nonnegative 0
  have p1 := nonnegative 1
  have p2 := nonnegative 2
  let inputs := fun slot : Fin 4 => actualCartesianPrimitiveCurve parameters length lower positive bounded source slot grade
  let first := fun radius => hilbertSlotInjection parameters 4 (inputs 0 radius)
  let second := fun radius => hilbertSlotInjection parameters 5 (inputs 1 radius)
  let third := fun radius => hilbertSlotInjection parameters 6 (inputs 2 radius)
  have measurable (slot : Fin 4) : AEStronglyMeasurable (inputs slot) (volume.restrict (Icc lower 1)) :=
    ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).smooth grade).continuousOn.aestronglyMeasurable measurableSet_Icc
  have firstM : AEStronglyMeasurable first (volume.restrict (Icc lower 1)) :=
    (hilbertSlotInjection parameters 4).continuous.comp_aestronglyMeasurable (measurable 0)
  have secondM : AEStronglyMeasurable second (volume.restrict (Icc lower 1)) :=
    (hilbertSlotInjection parameters 5).continuous.comp_aestronglyMeasurable (measurable 1)
  have thirdM : AEStronglyMeasurable third (volume.restrict (Icc lower 1)) :=
    (hilbertSlotInjection parameters 6).continuous.comp_aestronglyMeasurable (measurable 2)
  have firstE := boundedAction_squareEnergy lower (hilbertSlotInjection parameters 4) (inputs 0) (payments 0) (energy 0)
  have secondE := boundedAction_squareEnergy lower (hilbertSlotInjection parameters 5) (inputs 1) (payments 1) (energy 1)
  have thirdE := boundedAction_squareEnergy lower (hilbertSlotInjection parameters 6) (inputs 2) (payments 2) (energy 2)
  have pairE := twoInput_squareEnergy (volume.restrict (Icc lower 1)) (fun radius => first radius+second radius)
    first second firstM secondM 1 1 _ _ (by norm_num) (by norm_num)
    (mul_nonneg (norm_nonneg _) (nonnegative 0)) (mul_nonneg (norm_nonneg _) (nonnegative 1))
    (Filter.Eventually.of_forall (fun radius => by simpa only [one_mul] using norm_add_le (first radius) (second radius))) firstE secondE
  have allE := twoInput_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => (first radius+second radius)+third radius)
    (fun radius => first radius+second radius) third (firstM.add secondM) thirdM 1 1 _ _ (by norm_num) (by norm_num)
    (by positivity) (mul_nonneg (norm_nonneg _) (nonnegative 2))
    (Filter.Eventually.of_forall (fun radius => by simpa only [one_mul] using norm_add_le (first radius+second radius) (third radius))) pairE thirdE
  apply allE.trans
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_nonneg (norm_nonneg (hilbertSlotInjection parameters 6)) (nonnegative 2)]

/-- The SAME three known source curves have a sharp high q+4 energy and
an independent base F4 energy, ready for the actual two-input row kernel. -/
theorem actualKnownSeven_fourEnergy (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) :
    ∃ highConstant baseConstant : ℝ, 0 ≤ highConstant ∧ 0 ≤ baseConstant ∧
    ∀ source : SmoothQuotient parameters,
      ((∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖actualCartesianKnownSevenCurve parameters length lower positive bounded source (grade+1) radius‖^2)) ≤
        ENNReal.ofReal ((highConstant*‖quotientEta parameters (grade+4) source‖)^2)) ∧
      ((∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖actualCartesianKnownSevenCurve parameters length lower positive bounded source 0 radius‖^2)) ≤
        ENNReal.ofReal ((baseConstant*‖quotientEta parameters 4 source‖)^2)) := by
  obtain ⟨high,highNonnegative,highEnergy⟩ := actualPrimitiveCurve_fourEnergy parameters length lower positive bounded grade
  obtain ⟨low,lowNonnegative,lowEnergy⟩ := actualPrimitiveCurve_baseEnergy parameters length lower positive bounded
  let packed := fun constants : Fin 4 → ℝ => 4*(‖hilbertSlotInjection parameters 4‖*constants 0 +
    ‖hilbertSlotInjection parameters 5‖*constants 1 + ‖hilbertSlotInjection parameters 6‖*constants 2)
  have packed0 (constants : Fin 4 → ℝ) (nonnegative : ∀ slot,0 ≤ constants slot) : 0 ≤ packed constants := by
    exact mul_nonneg (by norm_num) (add_nonneg
      (add_nonneg (mul_nonneg (norm_nonneg _) (nonnegative 0))
        (mul_nonneg (norm_nonneg _) (nonnegative 1)))
      (mul_nonneg (norm_nonneg _) (nonnegative 2)))
  have packed_mul (constants : Fin 4 → ℝ) (value : ℝ) :
      4*(‖hilbertSlotInjection parameters 4‖*(constants 0*value)+
        ‖hilbertSlotInjection parameters 5‖*(constants 1*value)+
        ‖hilbertSlotInjection parameters 6‖*(constants 2*value)) = packed constants*value := by
    dsimp only [packed]
    ring
  refine ⟨packed high,packed low,packed0 high highNonnegative,packed0 low lowNonnegative,?_⟩
  intro source
  constructor
  · simpa only [packed_mul] using sameKnownSeven_energy parameters length lower positive bounded source (grade+1)
      (fun slot => high slot*‖quotientEta parameters (grade+4) source‖)
      (fun slot => mul_nonneg (highNonnegative slot) (norm_nonneg _)) (highEnergy source)
  · simpa only [packed_mul] using sameKnownSeven_energy parameters length lower positive bounded source 0
      (fun slot => low slot*‖quotientEta parameters 4 source‖)
      (fun slot => mul_nonneg (lowNonnegative slot) (norm_nonneg _)) (lowEnergy source)

end Grad.OriginalCartesianTameEstimate
