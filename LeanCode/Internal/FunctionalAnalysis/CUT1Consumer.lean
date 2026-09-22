import CUT1Derivatives
import CUT1Disk

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open Grad.WeightedJets (TestFunction JetIndex testPairing testPairing_apply)
open scoped ContDiff Topology

namespace Grad.CompactCutoff

theorem multiplyTest_support {compactSet domain targetDomain : Set Spatial}
    (cutoff : Cutoff compactSet domain) (test : TestFunction targetDomain) :
    tsupport (multiplyTest cutoff test).toFun ⊆ tsupport cutoff.toFun ∩ tsupport test.toFun :=
  Set.subset_inter tsupport_mul_subset_left tsupport_mul_subset_right

theorem multiplyTest_eq {compactSet domain targetDomain : Set Spatial}
    (cutoff : Cutoff compactSet domain) (test : TestFunction targetDomain)
    (supported : tsupport test.toFun ⊆ compactSet) :
    (multiplyTest cutoff test).toFun = test.toFun := by
  funext point
  change cutoff.toFun point * test.toFun point = test.toFun point
  by_cases membership : point ∈ tsupport test.toFun
  · rw [cutoff.one_on (supported membership), one_mul]
  · rw [image_eq_zero_of_notMem_tsupport membership, mul_zero]

theorem test_consumer : TestGoal := by
  intro compactSet domain targetDomain cutoff test
  refine ⟨rfl, multiplyTest_support cutoff test, multiplyTest_eq cutoff test, ?_⟩
  intro dimension openTarget field cell vector
  have pairing := Grad.WeightedJets.SpatialMultiplier.fieldMultiplier_pairing
    dimension targetDomain openTarget (boundedScalar cutoff targetDomain) field cell vector test
  refine ⟨pairing, ?_⟩
  rw [testPairing_apply, testPairing_apply] at pairing
  exact pairing

theorem cutoffSymbol_bound {compactSet domain : Set Spatial} (cutoff : Cutoff compactSet domain)
    (order : ℕ) (targetDomain : Set Spatial) (index : JetIndex order) (point : Spatial) :
    |Grad.WeightedJets.SpatialMultiplier.scalarDerivative index.val cutoff.toFun point| ≤
      (cutoffSymbol cutoff order targetDomain).bound index :=
  (Grad.WeightedJets.SpatialMultiplier.compactDerivative_bound index.val
    cutoff.toFun cutoff.smooth cutoff.compact).choose_spec point

theorem multiplier_consumer : MultiplierGoal := by
  intro compactSet domain cutoff
  refine ⟨fun order targetDomain => ⟨rfl, cutoffSymbol_bound cutoff order targetDomain⟩, ?_, ?_, ?_⟩
  · intro dimension order targetDomain openTarget exponent compatible
    exact Grad.WeightedJets.SpatialMultiplier.compactJetMultiplier_laws
      dimension order targetDomain openTarget cutoff.toFun cutoff.smooth cutoff.compact exponent compatible
  · intro dimension order weight targetDomain openTarget
    exact Grad.WeightedJets.SpatialMultiplier.graphMultiplier_laws
      dimension order weight targetDomain openTarget (cutoffSymbol cutoff order targetDomain)
  · intro dimension grade targetDomain openTarget
    exact Grad.WeightedJets.SpatialMultiplier.mixedMultiplier_laws
      dimension grade targetDomain openTarget (cutoffSymbol cutoff grade targetDomain)

theorem compactCutoff_properties (compactSet domain : Set Spatial)
    (compactSetCompact : IsCompact compactSet) (openDomain : IsOpen domain)
    (included : compactSet ⊆ domain) :
    let cutoff := compactCutoff compactSet domain compactSetCompact openDomain included
    ContDiff ℝ ∞ cutoff.toFun ∧ HasCompactSupport cutoff.toFun ∧
      (∀ point, 0 ≤ cutoff.toFun point ∧ cutoff.toFun point ≤ 1) ∧
      tsupport cutoff.toFun ⊆ domain ∧
      (∃ neighborhood : Set Spatial, IsOpen neighborhood ∧ compactSet ⊆ neighborhood ∧
        neighborhood ⊆ domain ∧ Set.EqOn cutoff.toFun (fun _ => 1) neighborhood) ∧
      (∀ point ∈ compactSet, cutoff.toFun =ᶠ[𝓝 point] (fun _ => 1)) ∧
      ∀ (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial),
        |Grad.WeakTesting.orderedTestDerivative rank word cutoff.toFun point| ≤ orderedBound cutoff word := by
  let cutoff := compactCutoff compactSet domain compactSetCompact openDomain included
  exact ⟨cutoff.smooth, cutoff.compact, fun point => ⟨cutoff.nonnegative point, cutoff.atMostOne point⟩,
    cutoff.supported, cutoff.near, cutoff.germ, orderedDerivative_bound cutoff⟩

theorem compactCutoff_multiplier (compactSet domain : Set Spatial)
    (compactSetCompact : IsCompact compactSet) (openDomain : IsOpen domain)
    (included : compactSet ⊆ domain) (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (compatible : Grad.WeightedJets.SpatialMultiplier.ExponentAntitone exponent) :
    let cutoff := compactCutoff compactSet domain compactSetCompact openDomain included
    Grad.WeightedJets.SpatialMultiplier.JetMultiplierLaws dimension order domain openDomain
      (cutoffSymbol cutoff order domain) exponent
      (Grad.WeightedJets.SpatialMultiplier.compactJetMultiplier dimension order domain openDomain
        cutoff.toFun cutoff.smooth cutoff.compact exponent compatible) :=
  (multiplier_consumer compactSet domain
    (compactCutoff compactSet domain compactSetCompact openDomain included)).2.1
      dimension order domain openDomain exponent compatible

theorem block_consumer : BlockGoal :=
  ⟨cover_consumer, finite_product_consumer, existence_consumer, ordered_derivative_consumer,
    disk_consumer, test_consumer, multiplier_consumer⟩

end Grad.CompactCutoff
