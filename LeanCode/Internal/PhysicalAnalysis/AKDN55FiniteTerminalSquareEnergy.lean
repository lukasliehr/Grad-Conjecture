import AKDN51SignedEulerEnergyAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.OriginalCartesianTameEstimate

theorem finiteSum_aestronglyMeasurable {Index Point Value : Type*} [MeasurableSpace Point]
    [NormedAddCommGroup Value] (measure : Measure Point) (curves : Index → Point → Value)
    (measurable : ∀ index, AEStronglyMeasurable (curves index) measure) (terms : Finset Index) :
    AEStronglyMeasurable (fun point => ∑ index ∈ terms, curves index point) measure := by
  classical
  induction terms using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Point => (0:Value)) measure)
  | @insert index terms absent previous =>
      apply ((measurable index).add previous).congr
      apply Filter.Eventually.of_forall
      intro point
      change curves index point+(∑ current ∈ terms, curves current point) =
        ∑ current ∈ insert index terms, curves current point
      rw [Finset.sum_insert absent]

/-- Integrate the exact filtered finite terminal sum. Only allocations
present in the native induction require energy bounds. -/
theorem finiteEulerTerminal_squareEnergy (measure : Measure ℝ) (total : ℕ) (budget : ℕ → ℝ)
    (unknown forcing : ℕ → ℕ → ℝ → ℝ) (payment : ℝ) (payment0 : 0 ≤ payment)
    (unknownMeasurable : ∀ grade, AEStronglyMeasurable (unknown 0 grade) measure)
    (forcingMeasurable : ∀ order grade, AEStronglyMeasurable (forcing order grade) measure)
    (pureEnergy : ∀ extra grade, extra+grade≤total →
      (∫⁻ radius, ENNReal.ofReal (‖budget extra*unknown 0 grade radius‖^2) ∂measure) ≤ ENNReal.ofReal (payment^2))
    (sourceEnergy : ∀ extra order grade, extra+order+grade+1≤total →
      (∫⁻ radius, ENNReal.ofReal (‖budget extra*forcing order grade radius‖^2) ∂measure) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ radius, ENNReal.ofReal
      ((finiteEulerTerminal total budget (fun order grade => unknown order grade radius)
        (fun order grade => forcing order grade radius))^2) ∂measure) ≤
      ENNReal.ofReal (((2*((4:ℝ)^(Finset.univ : Finset (Fin (total+1) × Fin (total+1))).card+
        (4:ℝ)^(Finset.univ : Finset (Fin (total+1) × Fin (total+1) × Fin (total+1))).card))*payment)^2) := by
  classical
  let pure := fun (index : Fin (total+1) × Fin (total+1)) radius =>
    if index.1.val+index.2.val≤total then budget index.1.val*unknown 0 index.2.val radius else 0
  let source := fun (index : Fin (total+1) × Fin (total+1) × Fin (total+1)) radius =>
    if index.1.val+index.2.1.val+index.2.2.val+1≤total then budget index.1.val*forcing index.2.1.val index.2.2.val radius else 0
  have pureM (index) : AEStronglyMeasurable (pure index) measure := by
    dsimp only [pure]
    split_ifs
    · exact (unknownMeasurable _).const_mul _
    · exact aestronglyMeasurable_const
  have sourceM (index) : AEStronglyMeasurable (source index) measure := by
    dsimp only [source]
    split_ifs
    · exact (forcingMeasurable _ _).const_mul _
    · exact aestronglyMeasurable_const
  have pureE (index) : (∫⁻ radius, ENNReal.ofReal (‖pure index radius‖^2) ∂measure) ≤ ENNReal.ofReal (payment^2) := by
    dsimp only [pure]
    split_ifs with paid
    · exact pureEnergy _ _ paid
    · simp only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
      exact bot_le
  have sourceE (index) : (∫⁻ radius, ENNReal.ofReal (‖source index radius‖^2) ∂measure) ≤ ENNReal.ofReal (payment^2) := by
    dsimp only [source]
    split_ifs with paid
    · exact sourceEnergy _ _ _ paid
    · simp only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
      exact bot_le
  have first := finiteSum_squareEnergy measure pure pureM payment payment0 pureE Finset.univ
  have second := finiteSum_squareEnergy measure source sourceM payment payment0 sourceE Finset.univ
  have actual := twoInput_squareEnergy measure
    (fun radius => (∑ index, pure index radius)+(∑ index, source index radius))
    (fun radius => ∑ index, pure index radius) (fun radius => ∑ index, source index radius)
    (finiteSum_aestronglyMeasurable measure pure pureM Finset.univ)
    (finiteSum_aestronglyMeasurable measure source sourceM Finset.univ)
    1 1 _ _ zero_le_one zero_le_one (by positivity) (by positivity)
    (Filter.Eventually.of_forall (fun _ => by simpa only [one_mul] using norm_add_le _ _)) first second
  have same (radius : ℝ) : (∑ index, pure index radius)+(∑ index, source index radius) =
      finiteEulerTerminal total budget (fun order grade => unknown order grade radius)
        (fun order grade => forcing order grade radius) := rfl
  simp only [same,Real.norm_eq_abs,sq_abs] at actual
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate
