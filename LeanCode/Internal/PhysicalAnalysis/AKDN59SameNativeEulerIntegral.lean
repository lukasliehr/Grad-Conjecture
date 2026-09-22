import AKDN58UniformSameForcingEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularStrongSolution Grad.AnnularKernelL2
open Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Allocation Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse

/-- The actual ordered native Euler recurrence is integrated. The only
remaining native inputs are the independent pure-frequency high/base energies
of the SAME balanced solution; every forcing term is paid by the actual source. -/
theorem sameNativeBalanced_jointEulerIntegral (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (total : ℕ) (totalPositive : 0 < total) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
        coupledPrimitiveRadius parameters length compact)
      (source : SmoothQuotient parameters) (flat : IsFlat source)
      (original : OriginalStrongCarrier parameters lower 0 0)
      (sameSources : original.val.ofLp.1 =
        (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
          lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1),
    let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
    let data := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 original
    let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    let balanced := balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response
    (∀ power : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive power response weighted) →
    ∀ high base : ℝ, 0 ≤ high → 0 ≤ base →
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖balanced total radius‖^2)) ≤ ENNReal.ofReal (high^2) →
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖balanced 0 radius‖^2)) ≤ ENNReal.ofReal (base^2) →
    ∀ extra grade order : ℕ, extra+grade+order ≤ total →
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) order (balanced grade) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(high+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*base+
        (‖quotientEta parameters (4+total) source‖+
          (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
            ‖quotientEta parameters 4 source‖)))^2) := by
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num : (1:ℝ)/2<1)
  let inductionResult := sameNativeBalanced_finiteEuler parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength total
  let gain := inductionResult.choose
  have gainOne := inductionResult.choose_spec.1
  have inductionBound := inductionResult.choose_spec.2
  let sourceResult := sameIncomingBalancedSource_uniformEulerEnergy parameters length compact lower
    positive bounded lengthPositive total
  let sourceConstant := sourceResult.choose
  have source0 := sourceResult.choose_spec.1
  have sourceBound := sourceResult.choose_spec.2
  let pureConstant := 4*(1+physicalInterpolationConstant 10 total)
  have pure0 : 0 ≤ pureConstant := by
    have one := physicalInterpolationConstant_one_le 10 total
    dsimp only [pureConstant]
    positivity
  let kernelNorm := ‖physicalPairMeanFree parameters‖
  have kernel0 : 0 ≤ kernelNorm := norm_nonneg _
  let terminalConstant := pureConstant+kernelNorm*sourceConstant
  have terminalConstant0 : 0 ≤ terminalConstant := add_nonneg pure0 (mul_nonneg kernel0 source0)
  let finiteFactor := 2*((4:ℝ)^(Finset.univ : Finset (Fin (total+1) × Fin (total+1))).card+
    (4:ℝ)^(Finset.univ : Finset (Fin (total+1) × Fin (total+1) × Fin (total+1))).card)
  have finite0 : 0 ≤ finiteFactor := by positivity
  have gain0 : 0 ≤ gain := zero_le_one.trans gainOne
  refine ⟨gain^total*finiteFactor*terminalConstant,by positivity,?_⟩
  intro state unit small source flat original sameSources
  dsimp only
  let data := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 original
  let curves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded lengthPositive source flat original sameSources
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let balanced := balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response
  intro allGrades high base high0 base0 highEnergy baseEnergy extra grade order allocated
  let budget := fun rank => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+rank)
  let forcingCurve := fun rank point => balancedActualSource parameters length compact lower positive bounded state data curves rank
    (collarRadius lower positive bounded.le point)
  let unknown := fun order grade radius => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (balanced grade) radius‖
  let forcing := fun order grade radius => kernelNorm*‖vectorEulerWithinIteratedDerivative (Icc lower 1) order (forcingCurve grade) radius‖
  let sourcePayment := ‖quotientEta parameters (4+total) source‖+budget total*‖quotientEta parameters 4 source‖
  let purePayment := high+budget total*base
  let payment := purePayment+sourcePayment
  have budget0 (rank : ℕ) : 0 ≤ budget rank := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have sourcePayment0 : 0 ≤ sourcePayment := add_nonneg (norm_nonneg _) (mul_nonneg (budget0 _) (norm_nonneg _))
  have purePayment0 : 0 ≤ purePayment := add_nonneg high0 (mul_nonneg (budget0 _) base0)
  have payment0 : 0 ≤ payment := add_nonneg purePayment0 sourcePayment0
  have nativeSmooth (rank : ℕ) : ContDiffOn ℝ ∞ (balanced rank) (Icc lower 1) :=
    sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small data curves allGrades rank
  have forceSmooth (rank : ℕ) : ContDiffOn ℝ ∞ (forcingCurve rank) (Icc lower 1) :=
    balancedActualSourceCurve_smooth parameters length compact lower positive lowerHalf state data curves rank
  have unknownM (rank : ℕ) : AEStronglyMeasurable (unknown 0 rank) (volume.restrict (Icc lower 1)) :=
    ((nativeSmooth rank).continuousOn.aestronglyMeasurable measurableSet_Icc).norm
  have forcingM (order rank : ℕ) : AEStronglyMeasurable (forcing order rank) (volume.restrict (Icc lower 1)) :=
    (((vectorEulerWithin_smooth (Icc lower 1) (uniqueDiffOn_Icc bounded) (forcingCurve rank) order 0
      (by simpa only [Nat.zero_add] using contDiffOn_infty.mp (forceSmooth rank) order)).continuousOn.aestronglyMeasurable
        measurableSet_Icc).norm).const_mul kernelNorm
  have same (rank : ℕ) : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      hilbertPairCoefficient mode (balanced rank radius)=(annularFrequency mode.1 mode.2 : ℂ)^rank •
        hilbertPairCoefficient mode (balanced 0 radius) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    intro mode
    simpa only [Nat.zero_add] using balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive
      response allGrades 0 rank radius inside mode
  have pureE (extra rank : ℕ) (paid : extra+rank≤total) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖budget extra*unknown 0 rank radius‖^2)) ≤
        ENNReal.ofReal ((terminalConstant*payment)^2) := by
    have actual := purePair_jointEnergy parameters state.val.val.field state.val.val.rho state.val.val.epsilon
      total extra rank totalPositive paid unit (volume.restrict (Icc lower 1)) (balanced 0) (balanced rank) (balanced total)
      ((nativeSmooth 0).continuousOn.aestronglyMeasurable measurableSet_Icc)
      ((nativeSmooth total).continuousOn.aestronglyMeasurable measurableSet_Icc) (same rank) (same total)
      high base high0 base0 highEnergy baseEnergy
    have sameEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖budget extra*unknown 0 rank radius‖^2)) =
        (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖budget extra • balanced rank radius‖^2)) := by
      apply lintegral_congr
      intro radius
      change ENNReal.ofReal (‖budget extra*‖balanced rank radius‖‖^2)=_
      rw [Real.norm_of_nonneg (mul_nonneg (budget0 _) (norm_nonneg _)),norm_smul,Real.norm_of_nonneg (budget0 _)]
    apply sameEnergy.le.trans (actual.trans _)
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (mul_nonneg pure0 purePayment0) (mul_nonneg terminalConstant0 payment0)).mpr
    have one : pureConstant≤terminalConstant := le_add_of_nonneg_right (mul_nonneg kernel0 source0)
    exact mul_le_mul one (le_add_of_nonneg_right sourcePayment0) purePayment0 terminalConstant0
  have sourceE (extra order rank : ℕ) (paid : extra+order+rank+1≤total) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖budget extra*forcing order rank radius‖^2)) ≤
        ENNReal.ofReal ((terminalConstant*payment)^2) := by
    have actual := sourceBound state unit source flat original sameSources extra rank order (by omega)
    have scaled := dominated_squareEnergy (volume.restrict (Icc lower 1))
      (fun radius => budget extra*forcing order rank radius)
      (fun radius => ‖budget extra • vectorEulerWithinIteratedDerivative (Icc lower 1) order (forcingCurve rank) radius‖)
      kernelNorm (sourceConstant*sourcePayment) kernel0 (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (by
        apply Filter.Eventually.of_forall
        intro radius
        dsimp only [forcing]
        rw [Real.norm_of_nonneg (mul_nonneg (budget0 _) (mul_nonneg kernel0 (norm_nonneg _))),norm_smul,
          Real.norm_of_nonneg (budget0 _)]
        exact (mul_left_comm _ _ _).le) (by simpa only [norm_norm] using actual)
    apply scaled.trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (mul_nonneg kernel0 (mul_nonneg source0 sourcePayment0)) (mul_nonneg terminalConstant0 payment0)).mpr
    have one : kernelNorm*sourceConstant≤terminalConstant := le_add_of_nonneg_left pure0
    have bound := mul_le_mul one (le_add_of_nonneg_left purePayment0) sourcePayment0 terminalConstant0
    nlinarith only [bound]
  have terminalEnergy := finiteEulerTerminal_squareEnergy (volume.restrict (Icc lower 1)) total budget unknown forcing
    (terminalConstant*payment) (mul_nonneg terminalConstant0 payment0) unknownM forcingM pureE sourceE
  have actual := dominated_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => budget extra • vectorEulerWithinIteratedDerivative (Icc lower 1) order (balanced grade) radius)
    (fun radius => finiteEulerTerminal total budget (fun order rank => unknown order rank radius) (fun order rank => forcing order rank radius))
    (gain^total) (finiteFactor*(terminalConstant*payment)) (pow_nonneg gain0 _)
    (Filter.Eventually.of_forall (fun _ => finiteEulerTerminal_nonnegative total budget _ _ budget0
      (fun _ _ => norm_nonneg _) (fun _ _ => mul_nonneg kernel0 (norm_nonneg _)))) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      rw [norm_smul,Real.norm_of_nonneg (budget0 extra)]
      exact inductionBound state unit small data curves allGrades ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩ inside
        order extra grade allocated) terminalEnergy
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate
