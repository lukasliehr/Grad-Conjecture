import AAZ15FinitePrefixNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace







section Recurrence
variable (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower)
    (jetGrades : ∀ index grade, HasAnnularRawStateGrade lower grade
      (annularPhysicalStateJet lower positive length initial source index))
    (sourceGrades : ∀ index grade, HasAnnularRawSourceGrade lower grade (source index))
    (order grade : ℕ)

include lengthPositive in
/-- The first component of AG34, with all coefficient losses displayed. -/
theorem annularPhysicalJet_p_bound :
    let jet := annularPhysicalStateJet lower positive length initial source
    ‖annularRawWeighted lower grade (jet (order + 1)).1 (jetGrades (order + 1) grade).1‖ ≤
      (annularLeibnizConstant lower 1 order + annularLeibnizConstant lower 2 order + 1 / (3 * length ^ 2)) *
        annularJetPrefixSize lower (grade + 2) order jet jetGrades +
      ‖annularRawWeighted lower (grade + 1) (source order).2.1 (sourceGrades order (grade + 1)).2.1‖ +
      (1 / (3 * length)) * ‖annularRawWeighted lower (grade + 1) (source order).2.2 (sourceGrades order (grade + 1)).2.2‖ := by
  let jet := annularPhysicalStateJet lower positive length initial source
  let size := annularJetPrefixSize lower (grade + 2) order jet jetGrades
  have pMember := annularRawGrade_leibniz lower positive grade 1 order (fun index => (jet index).1)
    (fun index _ => (jetGrades index grade).1)
  have squareMember := annularRawGrade_leibniz lower positive (grade + 1) 2 order (fun index => (jet index).2)
    (fun index _ => (jetGrades index (grade + 1)).2)
  have angularBound (mode : HighAnnularMode) : ‖annularAngularISymbol mode‖ ≤ 1 *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 1 := by
    simpa only [one_mul, pow_one] using annularAngularISymbol_bound mode
  have angularMember := annularRawGrade_symbol lower grade 1 annularAngularISymbol 1 zero_le_one angularBound _ squareMember
  have longitudinalMember := annularRawGrade_symbol lower grade 2 (annularLongitudinalISymbol length)
    (1 / (3 * length ^ 2)) (by positivity) (annularLongitudinalISymbol_bound length lengthPositive)
    _ (jetGrades order (grade + 2)).2
  have gMember := annularRawGrade_lower lower grade 1 (source order).2.1 (sourceGrades order (grade + 1)).2.1
  have forcingBound (mode : HighAnnularMode) : ‖annularLongitudinalSourceSymbol length mode‖ ≤
      (1 / (3 * length)) * (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 1 := by
    simpa only [pow_one] using annularLongitudinalSourceSymbol_bound length lengthPositive mode
  have forcingMember := annularRawGrade_symbol lower grade 1 (annularLongitudinalSourceSymbol length)
    (1 / (3 * length)) (by positivity) forcingBound _ (sourceGrades order (grade + 1)).2.2
  have equality := congrArg Prod.fst (annularPhysicalStateJet_succ lower positive length initial source order)
  have target := (congrArg (HasAnnularRawGrade lower grade) equality).mp (jetGrades (order + 1) grade).1
  have triangle := (annularRawWeighted_norm_congr lower grade _ _ (jetGrades (order + 1) grade).1 target equality).le.trans
    (annularRawWeighted_five_bound lower grade _ _ _ _ _ pMember angularMember longitudinalMember gMember forcingMember target)
  have pEstimate := annularRawWeighted_leibniz_bound lower positive grade 1 order (fun index => (jet index).1)
    (fun index => (jetGrades index grade).1) pMember size
    (fun index bound => (annularJetPrefixSize_component lower grade (grade + 2) order (by omega) jet jetGrades index bound).1)
  have squareEstimate := annularRawWeighted_leibniz_bound lower positive (grade + 1) 2 order (fun index => (jet index).2)
    (fun index => (jetGrades index (grade + 1)).2) squareMember size
    (fun index bound => (annularJetPrefixSize_component lower (grade + 1) (grade + 2) order (by omega) jet jetGrades index bound).2)
  have angularEstimate := annularRawWeighted_symbol_bound lower grade 1 annularAngularISymbol 1 zero_le_one angularBound
    _ squareMember angularMember
  have longitudinalEstimate := annularRawWeighted_symbol_bound lower grade 2 (annularLongitudinalISymbol length)
    (1 / (3 * length ^ 2)) (by positivity) (annularLongitudinalISymbol_bound length lengthPositive)
    _ (jetGrades order (grade + 2)).2 longitudinalMember
  have longitudinalSize := mul_le_mul_of_nonneg_left
    (annularJetPrefixSize_component lower (grade + 2) (grade + 2) order le_rfl jet jetGrades order le_rfl).2
    (show 0 ≤ 1 / (3 * length ^ 2) by positivity)
  have gEstimate := annularRawWeighted_lower lower grade 1 _ (sourceGrades order (grade + 1)).2.1 gMember
  have forcingEstimate := annularRawWeighted_symbol_bound lower grade 1 (annularLongitudinalSourceSymbol length)
    (1 / (3 * length)) (by positivity) forcingBound _ (sourceGrades order (grade + 1)).2.2 forcingMember
  dsimp only
  change _ ≤ (annularLeibnizConstant lower 1 order + annularLeibnizConstant lower 2 order + 1 / (3 * length ^ 2)) * size + _ + _
  nlinarith

/-- The second component of AG34, with its original D multiplier. -/
theorem annularPhysicalJet_xi_bound :
    let jet := annularPhysicalStateJet lower positive length initial source
    ‖annularRawWeighted lower grade (jet (order + 1)).2 (jetGrades (order + 1) grade).2‖ ≤
      (2 * annularLeibnizConstant lower 1 order + 1) * annularJetPrefixSize lower (grade + 2) order jet jetGrades +
      ‖annularRawWeighted lower (grade + 1) (source order).1 (sourceGrades order (grade + 1)).1‖ := by
  let jet := annularPhysicalStateJet lower positive length initial source
  let size := annularJetPrefixSize lower (grade + 2) order jet jetGrades
  have radialMember := annularRawGrade_leibniz lower positive grade 1 order (fun index => (jet index).2)
    (fun index _ => (jetGrades index grade).2)
  have twiceMember := annularRawGrade_real lower grade (-2) _ radialMember
  have dBound (mode : HighAnnularMode) : ‖-annularDSymbol mode‖ ≤
      1 * (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 1 := by
    simpa only [norm_neg, one_mul, pow_one] using annularDSymbol_frequency_bound mode
  have dMember := annularRawGrade_symbol lower grade 1 (fun mode => -annularDSymbol mode) 1 zero_le_one dBound
    _ (jetGrades order (grade + 1)).1
  have fMember := annularRawGrade_lower lower grade 1 (source order).1 (sourceGrades order (grade + 1)).1
  have equality := congrArg Prod.snd (annularPhysicalStateJet_succ lower positive length initial source order)
  have target := (congrArg (HasAnnularRawGrade lower grade) equality).mp (jetGrades (order + 1) grade).2
  have triangle := (annularRawWeighted_norm_congr lower grade _ _ (jetGrades (order + 1) grade).2 target equality).le.trans
    (annularRawWeighted_three_bound lower grade _ _ _ twiceMember dMember fMember target)
  have radialEstimate := annularRawWeighted_leibniz_bound lower positive grade 1 order (fun index => (jet index).2)
    (fun index => (jetGrades index grade).2) radialMember size
    (fun index bound => (annularJetPrefixSize_component lower grade (grade + 2) order (by omega) jet jetGrades index bound).2)
  have twiceEstimate := annularRawWeighted_real_bound lower grade (-2) _ radialMember twiceMember
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at twiceEstimate
  have dEstimate := annularRawWeighted_symbol_bound lower grade 1 (fun mode => -annularDSymbol mode) 1 zero_le_one dBound
    _ (jetGrades order (grade + 1)).1 dMember
  have dSize := (annularJetPrefixSize_component lower (grade + 1) (grade + 2) order (by omega) jet jetGrades order le_rfl).1
  have fEstimate := annularRawWeighted_lower lower grade 1 _ (sourceGrades order (grade + 1)).1 fMember
  dsimp only
  change _ ≤ (2 * annularLeibnizConstant lower 1 order + 1) * size + _
  nlinarith

end Recurrence
end Grad.AnnularRadialJets
