import SM1Jet

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

theorem constantExponent_antitone (order weight : ℕ) :
    ExponentAntitone (fun _ : JetIndex order => weight) :=
  fun _ _ _ => le_rfl

theorem mixedExponent_antitone (grade : ℕ) :
    ExponentAntitone (fun index : JetIndex grade => grade - degree index) := by
  intro lower upper bound
  exact Nat.sub_le_sub_left (Nat.add_le_add bound.1 bound.2) grade

def graphMultiplier (dimension order weight : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) :
    GraphGrade dimension order weight domain →L[ℂ] GraphGrade dimension order weight domain :=
  jetMultiplier dimension order domain openDomain symbol (fun _ => weight)
    (constantExponent_antitone order weight)

def mixedMultiplier (dimension grade : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol grade domain) :
    Mixed dimension grade domain →L[ℂ] Mixed dimension grade domain :=
  jetMultiplier dimension grade domain openDomain symbol (fun index => grade - degree index)
    (mixedExponent_antitone grade)

theorem graphMultiplier_laws (dimension order weight : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) :
    JetMultiplierLaws dimension order domain openDomain symbol (fun _ => weight)
      (graphMultiplier dimension order weight domain openDomain symbol) :=
  jetMultiplier_laws dimension order domain openDomain symbol _ (constantExponent_antitone order weight)

theorem mixedMultiplier_laws (dimension grade : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol grade domain) :
    JetMultiplierLaws dimension grade domain openDomain symbol (fun index => grade - degree index)
      (mixedMultiplier dimension grade domain openDomain symbol) :=
  jetMultiplier_laws dimension grade domain openDomain symbol _ (mixedExponent_antitone grade)

theorem grade_consumer : GradeGoal :=
  ⟨fun dimension order weight domain openDomain symbol =>
    ⟨graphMultiplier dimension order weight domain openDomain symbol,
      graphMultiplier_laws dimension order weight domain openDomain symbol⟩,
    fun dimension grade domain openDomain symbol =>
    ⟨mixedMultiplier dimension grade domain openDomain symbol,
      mixedMultiplier_laws dimension grade domain openDomain symbol⟩⟩

theorem compactDerivative_bound (index : ℕ × ℕ) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) (compactSupport : HasCompactSupport scalar) :
    ∃ bound : NNReal, ∀ point : Spatial, |scalarDerivative index scalar point| ≤ bound := by
  have compactDerivative : HasCompactSupport (scalarDerivative index scalar) :=
    Grad.WeakTesting.orderedTestDerivative_hasCompactSupport _ _ scalar compactSupport
  obtain ⟨bound, estimate⟩ := compactDerivative.exists_bound_of_continuous
    (scalarDerivative_smooth index scalar smoothness).continuous
  refine ⟨⟨max bound 0, le_max_right _ _⟩, fun point => ?_⟩
  have literal : |scalarDerivative index scalar point| ≤ bound := by
    simpa only [Real.norm_eq_abs] using estimate point
  exact literal.trans (le_max_left _ _)

def compactSymbol (order : ℕ) (domain : Set Spatial) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) (compactSupport : HasCompactSupport scalar) :
    Symbol order domain where
  toFun := scalar
  smooth := smoothness
  bound index := (compactDerivative_bound index.val scalar smoothness compactSupport).choose
  derivative_bound index point _ :=
    (compactDerivative_bound index.val scalar smoothness compactSupport).choose_spec point

def compactJetMultiplier (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ scalar) (compactSupport : HasCompactSupport scalar)
    (exponent : JetIndex order → ℕ) (compatible : ExponentAntitone exponent) :
    WJet dimension order domain exponent →L[ℂ] WJet dimension order domain exponent :=
  jetMultiplier dimension order domain openDomain (compactSymbol order domain scalar smoothness compactSupport)
    exponent compatible

theorem compactJetMultiplier_laws (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ scalar) (compactSupport : HasCompactSupport scalar)
    (exponent : JetIndex order → ℕ) (compatible : ExponentAntitone exponent) :
    JetMultiplierLaws dimension order domain openDomain (compactSymbol order domain scalar smoothness compactSupport)
      exponent (compactJetMultiplier dimension order domain openDomain scalar smoothness compactSupport exponent compatible) :=
  jetMultiplier_laws dimension order domain openDomain _ exponent compatible

theorem compact_consumer : CompactGoal := by
  intro order domain scalar smoothness compactSupport
  refine ⟨compactSymbol order domain scalar smoothness compactSupport, rfl, ?_⟩
  intro dimension openDomain exponent compatible
  exact ⟨compactJetMultiplier dimension order domain openDomain scalar smoothness compactSupport exponent compatible,
    compactJetMultiplier_laws dimension order domain openDomain scalar smoothness compactSupport exponent compatible⟩

theorem fieldMultiplier_congr (dimension : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (first second : BoundedScalar domain) (same : first.toFun = second.toFun) :
    fieldMultiplier dimension domain openDomain first = fieldMultiplier dimension domain openDomain second := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [fieldMultiplier_ae dimension domain openDomain first field,
    fieldMultiplier_ae dimension domain openDomain second field] with point firstEq secondEq
  apply lp.ext
  funext cell
  rw [firstEq cell, secondEq cell, same]

theorem jetMultiplier_zero_coordinate (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    (jetMultiplier dimension order domain openDomain symbol exponent compatible jet).val (zeroIndex order) =
      fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
        (jet.val (zeroIndex order)) := by
  rw [jetMultiplier_coordinates, below_zero, Finset.sum_singleton, difference_self, binomial_self,
    Nat.cast_one, one_smul, Nat.sub_self, Grad.CellWeights.inverseFieldCLM_zero,
    ContinuousLinearMap.id_apply]

theorem jetMultiplier_inclusion (dimension lower higher : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target)
    (sourceAntitone : ExponentAntitone source) (targetAntitone : ExponentAntitone target)
    (sourceSymbol : Symbol higher domain) (targetSymbol : Symbol lower domain)
    (sameSymbol : sourceSymbol.toFun = targetSymbol.toFun) :
    (jetMultiplier dimension lower domain openDomain targetSymbol target targetAntitone).comp
        (Inclusions.inclusion dimension lower higher domain gap bound source target compatible) =
      (Inclusions.inclusion dimension lower higher domain gap bound source target compatible).comp
        (jetMultiplier dimension higher domain openDomain sourceSymbol source sourceAntitone) := by
  apply ContinuousLinearMap.ext
  intro jet
  apply base_injective dimension lower domain openDomain target
  simp only [ContinuousLinearMap.comp_apply, jetMultiplier_base_apply, Inclusions.inclusion_base]
  have equality := fieldMultiplier_congr dimension domain openDomain
    (derivativeScalar targetSymbol (zeroIndex lower)) (derivativeScalar sourceSymbol (zeroIndex higher))
    (show targetSymbol.toFun = sourceSymbol.toFun from sameSymbol.symm)
  rw [equality]

theorem block_consumer : BlockGoal :=
  ⟨field_consumer, scalar_consumer, weak_consumer, tuple_consumer, graph_consumer,
    jet_consumer, grade_consumer, compact_consumer⟩

end Grad.WeightedJets.SpatialMultiplier
