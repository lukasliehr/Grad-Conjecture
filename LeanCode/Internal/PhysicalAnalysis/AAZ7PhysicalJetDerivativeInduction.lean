import AAZ6RawGradeAlgebra

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

def AnnularPhysicalSourceJets (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (source : ℕ → AnnularRawSource lower) : Prop :=
  ∀ order,
    AnnularPhysicalWeakDerivative parameters lower positive (source order).1 (source (order + 1)).1 ∧
    AnnularPhysicalWeakDerivative parameters lower positive (source order).2.1 (source (order + 1)).2.1 ∧
    AnnularPhysicalWeakDerivative parameters lower positive (source order).2.2 (source (order + 1)).2.2

/-- Physical derivative membership propagates from the actual first weak
row, using only already proved lower derivatives and the prescribed source
jet chain. No higher solution derivative is a premise. -/
theorem annularPhysicalStateJet_weak (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (length : ℝ) (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower)
    (sourceWeak : AnnularPhysicalSourceJets parameters lower positive source)
    (initialWeak :
      AnnularPhysicalWeakDerivative parameters lower positive initial.1
        (annularPhysicalStateJet lower positive length initial source 1).1 ∧
      AnnularPhysicalWeakDerivative parameters lower positive initial.2
        (annularPhysicalStateJet lower positive length initial source 1).2)
    (order : ℕ) :
    AnnularPhysicalWeakDerivative parameters lower positive
      (annularPhysicalStateJet lower positive length initial source order).1
      (annularPhysicalStateJet lower positive length initial source (order + 1)).1 ∧
    AnnularPhysicalWeakDerivative parameters lower positive
      (annularPhysicalStateJet lower positive length initial source order).2
      (annularPhysicalStateJet lower positive length initial source (order + 1)).2 := by
  induction order using Nat.strong_induction_on with
  | h order previous =>
    cases order with
    | zero => simpa only [annularPhysicalStateJet_zero, zero_add] using initialWeak
    | succ order =>
      let jet := annularPhysicalStateJet lower positive length initial source
      have pWeak (index : ℕ) (bound : index ≤ order) :
          AnnularPhysicalWeakDerivative parameters lower positive (jet index).1 (jet (index + 1)).1 :=
        (previous index (Nat.lt_succ_of_le bound)).1
      have xiWeak (index : ℕ) (bound : index ≤ order) :
          AnnularPhysicalWeakDerivative parameters lower positive (jet index).2 (jet (index + 1)).2 :=
        (previous index (Nat.lt_succ_of_le bound)).2
      have pRadial := annularLeibniz_weak parameters lower positive 1 order (fun index => (jet index).1) pWeak
      have xiRadial := annularLeibniz_weak parameters lower positive 1 order (fun index => (jet index).2) xiWeak
      have xiSquare := annularLeibniz_weak parameters lower positive 2 order (fun index => (jet index).2) xiWeak
      have pFirst := annularPhysicalWeak_add parameters lower positive _ _ _ _ pRadial
        (annularPhysicalWeak_symbol parameters lower positive annularAngularISymbol _ _ xiSquare)
      have pSecond := annularPhysicalWeak_add parameters lower positive _ _ _ _ pFirst
        (annularPhysicalWeak_symbol parameters lower positive (annularLongitudinalISymbol length) _ _ (xiWeak order le_rfl))
      have pThird := annularPhysicalWeak_add parameters lower positive _ _ _ _ pSecond (sourceWeak order).2.1
      have pResult := annularPhysicalWeak_add parameters lower positive _ _ _ _ pThird
        (annularPhysicalWeak_symbol parameters lower positive (annularLongitudinalSourceSymbol length) _ _ (sourceWeak order).2.2)
      have xiFirst := annularPhysicalWeak_add parameters lower positive _ _ _ _
        (annularPhysicalWeak_real parameters lower positive (-2) _ _ xiRadial)
        (annularPhysicalWeak_symbol parameters lower positive (fun mode => -annularDSymbol mode) _ _ (pWeak order le_rfl))
      have xiResult := annularPhysicalWeak_add parameters lower positive _ _ _ _ xiFirst (sourceWeak order).1
      let property := fun first second : AnnularRawState lower =>
        AnnularPhysicalWeakDerivative parameters lower positive first.1 second.1 ∧
        AnnularPhysicalWeakDerivative parameters lower positive first.2 second.2
      exact (congrArg₂ property
        (annularPhysicalStateJet_succ lower positive length initial source order)
        (annularPhysicalStateJet_succ lower positive length initial source (order + 1))).mpr ⟨pResult, xiResult⟩

end Grad.AnnularRadialJets
