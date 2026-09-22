import SM1Consumer
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open Grad.WeightedJets (TestFunction JetIndex WJet testPairing)
open scoped BigOperators ContDiff Topology

namespace Grad.CompactCutoff

structure BumpCover (compactSet domain : Set Spatial) where
  count : ℕ
  center : Fin count → Spatial
  bump : ∀ index, ContDiffBump (center index)
  contained : ∀ index, Metric.closedBall (center index) (bump index).rOut ⊆ domain
  covers : compactSet ⊆ ⋃ index, Metric.ball (center index) (bump index).rIn

def BumpCover.innerRegion {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : Set Spatial :=
  ⋃ index, Metric.ball (cover.center index) (cover.bump index).rIn

def BumpCover.outerRegion {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : Set Spatial :=
  ⋃ index, Metric.closedBall (cover.center index) (cover.bump index).rOut

def BumpCover.toFun {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : Spatial → ℝ :=
  fun point => 1 - ∏ index : Fin cover.count, (1 - cover.bump index point)

structure Cutoff (compactSet domain : Set Spatial) where
  toFun : Spatial → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun
  nonnegative : ∀ point, 0 ≤ toFun point
  atMostOne : ∀ point, toFun point ≤ 1
  supported : tsupport toFun ⊆ domain
  near : ∃ neighborhood : Set Spatial, IsOpen neighborhood ∧ compactSet ⊆ neighborhood ∧
    neighborhood ⊆ domain ∧ Set.EqOn toFun (fun _ => 1) neighborhood

def CoverGoal : Prop :=
  ∀ (compactSet domain : Set Spatial), IsCompact compactSet → IsOpen domain →
    compactSet ⊆ domain → Nonempty (BumpCover compactSet domain)

def FiniteProductGoal : Prop :=
  ∀ (compactSet domain : Set Spatial) (cover : BumpCover compactSet domain),
    IsOpen cover.innerRegion ∧ compactSet ⊆ cover.innerRegion ∧
    cover.innerRegion ⊆ cover.outerRegion ∧ IsCompact cover.outerRegion ∧
    cover.outerRegion ⊆ domain ∧
    tsupport cover.toFun ⊆ cover.outerRegion ∧
    Set.EqOn cover.toFun (fun _ => 1) cover.innerRegion ∧
    ∃ cutoff : Cutoff compactSet domain, cutoff.toFun = cover.toFun

def ExistenceGoal : Prop :=
  ∀ (compactSet domain : Set Spatial), IsCompact compactSet → IsOpen domain →
    compactSet ⊆ domain → ∃ cutoff : Cutoff compactSet domain,
      (∃ cover : BumpCover compactSet domain, cutoff.toFun = cover.toFun) ∧
      ∀ point ∈ compactSet, cutoff.toFun =ᶠ[𝓝 point] (fun _ => 1)

def wordIndex {rank : ℕ} (word : Fin rank → Fin 2) : ℕ × ℕ :=
  ((List.ofFn word).count 0, (List.ofFn word).count 1)

def orderedBound {compactSet domain : Set Spatial} (cutoff : Cutoff compactSet domain)
    {rank : ℕ} (word : Fin rank → Fin 2) : NNReal :=
  (Grad.WeightedJets.SpatialMultiplier.compactDerivative_bound (wordIndex word) cutoff.toFun cutoff.smooth cutoff.compact).choose

def cutoffSymbol {compactSet domain : Set Spatial} (cutoff : Cutoff compactSet domain)
    (order : ℕ) (targetDomain : Set Spatial) : Grad.WeightedJets.SpatialMultiplier.Symbol order targetDomain :=
  Grad.WeightedJets.SpatialMultiplier.compactSymbol order targetDomain cutoff.toFun cutoff.smooth cutoff.compact

def boundedScalar {compactSet domain : Set Spatial} (cutoff : Cutoff compactSet domain)
    (targetDomain : Set Spatial) : Grad.WeightedJets.SpatialMultiplier.BoundedScalar targetDomain where
  toFun := cutoff.toFun
  smooth := cutoff.smooth
  bound := 1
  bound_on point _ := by
    rw [abs_of_nonneg (cutoff.nonnegative point)]
    exact cutoff.atMostOne point

def multiplyTest {compactSet domain targetDomain : Set Spatial}
    (cutoff : Cutoff compactSet domain) (test : TestFunction targetDomain) :
    TestFunction targetDomain :=
  Grad.WeightedJets.SpatialMultiplier.multiplyTest cutoff.toFun cutoff.smooth test

def OrderedDerivativeGoal : Prop :=
  ∀ (compactSet domain : Set Spatial) (cutoff : Cutoff compactSet domain),
    (∀ (rank : ℕ) (word : Fin rank → Fin 2),
      (wordIndex word).1 + (wordIndex word).2 = rank ∧
      Grad.WeakTesting.orderedTestDerivative rank word cutoff.toFun =
        Grad.WeightedJets.SpatialMultiplier.scalarDerivative (wordIndex word) cutoff.toFun ∧
      ContDiff ℝ ∞ (Grad.WeakTesting.orderedTestDerivative rank word cutoff.toFun) ∧
      HasCompactSupport (Grad.WeakTesting.orderedTestDerivative rank word cutoff.toFun) ∧
      tsupport (Grad.WeakTesting.orderedTestDerivative rank word cutoff.toFun) ⊆ tsupport cutoff.toFun ∧
      ∀ point : Spatial,
        |Grad.WeakTesting.orderedTestDerivative rank word cutoff.toFun point| ≤ orderedBound cutoff word) ∧
    (∀ word : Fin 0 → Fin 2,
      Grad.WeakTesting.orderedTestDerivative 0 word cutoff.toFun = cutoff.toFun ∧
      ∀ point : Spatial, |Grad.WeakTesting.orderedTestDerivative 0 word cutoff.toFun point| ≤ 1)

def diskBump (radius margin : ℝ) (nonnegativeRadius : 0 ≤ radius)
    (positiveMargin : 0 < margin) : ContDiffBump (0 : Spatial) where
  rIn := radius + margin
  rOut := radius + 2 * margin
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def DiskGoal : Prop :=
  ∀ (radius margin : ℝ) (nonnegativeRadius : 0 ≤ radius) (positiveMargin : 0 < margin),
    ∃ cutoff : Cutoff (Metric.closedBall (0 : Spatial) radius)
        (Metric.ball (0 : Spatial) (radius + 3 * margin)),
      cutoff.toFun = (diskBump radius margin nonnegativeRadius positiveMargin : Spatial → ℝ) ∧
      tsupport cutoff.toFun = Metric.closedBall (0 : Spatial) (radius + 2 * margin) ∧
      Set.EqOn cutoff.toFun (fun _ => 1) (Metric.closedBall (0 : Spatial) (radius + margin)) ∧
      (∀ point ∈ Metric.ball (0 : Spatial) (radius + margin),
        cutoff.toFun =ᶠ[𝓝 point] (fun _ => 1)) ∧
      Metric.closedBall (0 : Spatial) radius ⊆ Metric.ball (0 : Spatial) (radius + margin) ∧
      Metric.closedBall (0 : Spatial) (radius + 2 * margin) ⊆
        Metric.ball (0 : Spatial) (radius + 3 * margin)

def TestGoal : Prop :=
  ∀ (compactSet domain targetDomain : Set Spatial) (cutoff : Cutoff compactSet domain)
    (test : TestFunction targetDomain),
    (multiplyTest cutoff test).toFun = (fun point => cutoff.toFun point * test.toFun point) ∧
    tsupport (multiplyTest cutoff test).toFun ⊆ tsupport cutoff.toFun ∩ tsupport test.toFun ∧
    (tsupport test.toFun ⊆ compactSet → (multiplyTest cutoff test).toFun = test.toFun) ∧
    ∀ (dimension : ℕ) (openTarget : IsOpen targetDomain) (field : FieldL2 dimension targetDomain)
      (cell : ℤ) (vector : PhysicalValue dimension),
      testPairing dimension targetDomain cell vector test
          (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension targetDomain openTarget (boundedScalar cutoff targetDomain) field) =
        testPairing dimension targetDomain cell vector (multiplyTest cutoff test) field ∧
      (∫ point in targetDomain, test.toFun point • inner ℂ vector
          (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension targetDomain openTarget (boundedScalar cutoff targetDomain)
            field point cell)) =
        ∫ point in targetDomain, (cutoff.toFun point * test.toFun point) •
          inner ℂ vector (field point cell)

def MultiplierGoal : Prop :=
  ∀ (compactSet domain : Set Spatial) (cutoff : Cutoff compactSet domain),
    (∀ (order : ℕ) (targetDomain : Set Spatial),
      (cutoffSymbol cutoff order targetDomain).toFun = cutoff.toFun ∧
      ∀ (index : JetIndex order) (point : Spatial),
        |Grad.WeightedJets.SpatialMultiplier.scalarDerivative index.val cutoff.toFun point| ≤
          (cutoffSymbol cutoff order targetDomain).bound index) ∧
    (∀ (dimension order : ℕ) (targetDomain : Set Spatial) (openTarget : IsOpen targetDomain)
      (exponent : JetIndex order → ℕ) (compatible : Grad.WeightedJets.SpatialMultiplier.ExponentAntitone exponent),
      Grad.WeightedJets.SpatialMultiplier.JetMultiplierLaws dimension order targetDomain openTarget
        (cutoffSymbol cutoff order targetDomain) exponent
        (Grad.WeightedJets.SpatialMultiplier.compactJetMultiplier dimension order targetDomain openTarget
          cutoff.toFun cutoff.smooth cutoff.compact exponent compatible)) ∧
    (∀ (dimension order weight : ℕ) (targetDomain : Set Spatial) (openTarget : IsOpen targetDomain),
      Grad.WeightedJets.SpatialMultiplier.JetMultiplierLaws dimension order targetDomain openTarget
        (cutoffSymbol cutoff order targetDomain) (fun _ => weight)
        (Grad.WeightedJets.SpatialMultiplier.graphMultiplier dimension order weight targetDomain openTarget
          (cutoffSymbol cutoff order targetDomain))) ∧
    (∀ (dimension grade : ℕ) (targetDomain : Set Spatial) (openTarget : IsOpen targetDomain),
      Grad.WeightedJets.SpatialMultiplier.JetMultiplierLaws dimension grade targetDomain openTarget
        (cutoffSymbol cutoff grade targetDomain) (fun index => grade - Grad.WeightedJets.degree index)
        (Grad.WeightedJets.SpatialMultiplier.mixedMultiplier dimension grade targetDomain openTarget
          (cutoffSymbol cutoff grade targetDomain)))

def BlockGoal : Prop :=
  CoverGoal ∧ FiniteProductGoal ∧ ExistenceGoal ∧ OrderedDerivativeGoal ∧
    DiskGoal ∧ TestGoal ∧ MultiplierGoal

end Grad.CompactCutoff
