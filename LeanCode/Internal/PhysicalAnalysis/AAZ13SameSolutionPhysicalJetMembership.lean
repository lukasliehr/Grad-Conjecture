import AAZ12NoncircularJetMembership

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




/-- Every literal inserted grade of the actual zeroth physical state follows
from the accepted diagonal compatibility of the SAME inverse. -/
theorem annularOriginalRawState_grade (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (grade : ℕ)
    (dataGrade : HasAnnularDataGrade lower 0 0 grade (source, innerValue)) :
    HasAnnularRawStateGrade lower grade
      (annularOriginalRawState parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue) := by
  let data : AnnularForcing lower × AnnularBoundary := (source, innerValue)
  let weighted := annularWeightedData lower 0 0 grade data dataGrade
  let field := annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data
  let weightedField := annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength weighted
  have fieldLaw := annularInverse_decoded_weighted parameters lower length positive bounded lengthPositive widthHalf widthLength
    0 0 grade data dataGrade
  have sourceLaw : annularLpDecode 0 0 grade weighted.1.1 = source.1 :=
    annularLpDecode_weighted 0 0 grade source.1 dataGrade.1
  have qLaw := annularRecoveredQ_diagonal parameters lower length positive lengthPositive widthHalf widthLength
    (fun mode => (annularGradeWeight 0 0 grade mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound 0 0 grade) weightedField weighted.1.1
  have qDecode : annularLpDecode 0 0 grade
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength weightedField weighted.1.1) =
      annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 :=
    qLaw.symm.trans (congrArg₂ (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength)
      fieldLaw sourceLaw)
  have pCommutes := realLpDiagonal_commutes
    (fun mode => (annularGradeWeight 0 0 grade mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound 0 0 grade) (annularPMode lower) (12 / 5) (by norm_num)
    (annularPMode_bound lower)
    (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength weightedField weighted.1.1)
  have pDecode : annularLpDecode 0 0 grade
      (annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength weightedField weighted.1.1) =
      annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength field source.1 :=
    pCommutes.trans (congrArg (annularPMap lower) qDecode)
  have xiLaw := annularEnergyValue_diagonal lower length positive
    (fun mode => (annularGradeWeight 0 0 grade mode)⁻¹) 1 (by norm_num)
    (annularGradeWeight_inv_bound 0 0 grade) weightedField
  have xiDecode : annularLpDecode 0 0 grade (annularEnergyValue lower length positive weightedField) =
      annularEnergyValue lower length positive field :=
    xiLaw.symm.trans (congrArg (annularEnergyValue lower length positive) fieldLaw)
  exact ⟨(congrArg (HasAnnularLpGrade 0 0 grade) pDecode).mp (annularLpDecode_hasGrade 0 0 grade _),
    (congrArg (HasAnnularLpGrade 0 0 grade) xiDecode).mp (annularLpDecode_hasGrade 0 0 grade _)⟩

/-- All canonical jets of the actual solution are genuine physical weak
derivatives, with phase applied after the derivative. Only source jets are
prescribed; the initial solution row is derived from the original equations. -/
theorem annularOriginalStateJet_weak (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (sourceJet : ℕ → AnnularRawSource lower)
    (sourceZero : sourceJet 0 = annularOriginalRawSource lower source)
    (sourceWeak : AnnularPhysicalSourceJets parameters lower positive sourceJet) (order : ℕ) :
    let initial := annularOriginalRawState parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    let jet := annularPhysicalStateJet lower positive length initial sourceJet
    AnnularPhysicalWeakDerivative parameters lower positive (jet order).1 (jet (order + 1)).1 ∧
      AnnularPhysicalWeakDerivative parameters lower positive (jet order).2 (jet (order + 1)).2 := by
  dsimp only
  apply annularPhysicalStateJet_weak parameters lower positive length _ sourceJet sourceWeak _ order
  have initial := annularOriginalRawState_initialWeak parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  rw [annularPhysicalStateJet_one, sourceZero]
  exact initial

/-- Actual physical radial derivative membership at every finite inserted
grade, obtained without a hypothesis of solution derivative membership. -/
theorem annularOriginalStateJet_allGrades (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (sourceJet : ℕ → AnnularRawSource lower)
    (dataGrades : ∀ grade, HasAnnularDataGrade lower 0 0 grade (source, innerValue))
    (sourceGrades : ∀ order grade, HasAnnularRawSourceGrade lower grade (sourceJet order)) (order grade : ℕ) :
    HasAnnularRawStateGrade lower grade (annularPhysicalStateJet lower positive length
      (annularOriginalRawState parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
      sourceJet order) :=
  annularPhysicalStateJet_allGrades lower length positive lengthPositive _ sourceJet
    (fun grade => annularOriginalRawState_grade parameters lower length positive bounded lengthPositive widthHalf widthLength
      source innerValue grade (dataGrades grade)) sourceGrades order grade

end Grad.AnnularRadialJets
