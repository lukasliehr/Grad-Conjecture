import CellWeightsProof
import WT2Proof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets

def JetIndex (order : ℕ) := {multiIndex : ℕ × ℕ // multiIndex.1 + multiIndex.2 ≤ order}

instance indexFinite (order : ℕ) : Finite (JetIndex order) := by
  let encode : JetIndex order → Fin (order + 1) × Fin (order + 1) := fun index =>
    (⟨index.val.1, by have bound := index.property; omega⟩,
      ⟨index.val.2, by have bound := index.property; omega⟩)
  apply Finite.of_injective encode
  intro first second equality
  apply Subtype.ext
  exact congrArg (fun pair : Fin (order + 1) × Fin (order + 1) => (pair.1.val, pair.2.val)) equality

instance indexFintype (order : ℕ) : Fintype (JetIndex order) := Fintype.ofFinite _

def zeroIndex (order : ℕ) : JetIndex order := ⟨(0, 0), Nat.zero_le order⟩

def degree {order : ℕ} (index : JetIndex order) : ℕ := index.val.1 + index.val.2

def derivativeWord {order : ℕ} (index : JetIndex order) : Fin (degree index) → Fin 2 :=
  fun position => if position.val < index.val.1 then 0 else 1

structure TestFunction (domain : Set Spatial) where
  toFun : Spatial → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  supported : tsupport toFun ⊆ domain

abbrev JetTuple (dimension order : ℕ) (domain : Set Spatial) :=
  Grad.GenericCarriers.GraphTuple (JetIndex order) (fun _ => FieldL2 dimension domain)

def coordinate (dimension order : ℕ) (domain : Set Spatial) (index : JetIndex order) :
    JetTuple dimension order domain →L[ℂ] FieldL2 dimension domain :=
  Grad.GenericCarriers.graphProjection (JetIndex order) (fun _ => FieldL2 dimension domain) index

def ambientBase (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    JetTuple dimension order domain →L[ℂ] FieldL2 dimension domain :=
  (Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order))).comp
    (coordinate dimension order domain (zeroIndex order))

def testPairing (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) : FieldL2 dimension domain →L[ℂ] ℂ :=
  Grad.WeakTesting.compactPairing dimension domain cell vector test.toFun test.smooth test.compact

def derivativeTestPairing (dimension order : ℕ) (domain : Set Spatial) (index : JetIndex order)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) :
    FieldL2 dimension domain →L[ℂ] ℂ :=
  Grad.WeakTesting.orderedDerivativePairing dimension domain cell vector test.toFun test.smooth
    test.compact (degree index) (derivativeWord index)

def residual (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) :
    JetTuple dimension order domain →L[ℂ] ℂ :=
  (testPairing dimension domain cell vector test).comp (coordinate dimension order domain index) -
    ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) •
      (derivativeTestPairing dimension order domain index cell vector test).comp
        (ambientBase dimension order domain exponent)

def jetGraph (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    Submodule ℂ (JetTuple dimension order domain) :=
  ⨅ (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
    (residual dimension order domain exponent index cell vector test).ker

abbrev WJet (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :=
  jetGraph dimension order domain exponent

def base (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    WJet dimension order domain exponent →L[ℂ] FieldL2 dimension domain :=
  (ambientBase dimension order domain exponent).comp (jetGraph dimension order domain exponent).subtypeL

abbrev GraphGrade (dimension order weight : ℕ) (domain : Set Spatial) :=
  WJet dimension order domain (fun _ => weight)

abbrev Mixed (dimension grade : ℕ) (domain : Set Spatial) :=
  WJet dimension grade domain (fun index => grade - degree index)

def GraphGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ),
    IsClosed (jetGraph dimension order domain exponent : Set (JetTuple dimension order domain)) ∧
    (∀ tuple : JetTuple dimension order domain,
      tuple ∈ jetGraph dimension order domain exponent ↔
        ∀ (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
          testPairing dimension domain cell vector test (tuple index) =
            ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
              derivativeTestPairing dimension order domain index cell vector test
                (ambientBase dimension order domain exponent tuple)) ∧
    (∀ jet : WJet dimension order domain exponent, ‖jet‖ ^ 2 = ∑ index, ‖jet.val index‖ ^ 2)

def TopologyGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ),
    Grad.GenericCarriers.CompleteSeparable (WJet dimension order domain exponent)

def BaseGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ exponent : JetIndex order → ℕ,
      ‖base dimension order domain exponent‖ ≤ 1 ∧
      Function.Injective (base dimension order domain exponent) ∧
      (∀ jet : WJet dimension order domain exponent,
        base dimension order domain exponent jet =
          Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order))
            (jet.val (zeroIndex order)))

def IntegralGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain),
    tuple ∈ jetGraph dimension order domain exponent ↔
      ∀ (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
        (∫ point in domain, test.toFun point • inner ℂ vector (tuple index point cell)) =
          ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
            ∫ point in domain,
              Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
                inner ℂ vector (ambientBase dimension order domain exponent tuple point cell)

def BlockGoal : Prop := GraphGoal ∧ TopologyGoal ∧ BaseGoal ∧ IntegralGoal

end Grad.WeightedJets
