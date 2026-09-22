import WeakH1
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section

open MeasureTheory Grad.PDEBootstrap Function
open scoped ContDiff

namespace Grad.WeakTesting

abbrev Values (dimension : ℕ) := EuclideanSpace ℂ (Fin dimension)
abbrev Cells (dimension : ℕ) := lp (fun _ : ℤ => Values dimension) 2
abbrev Fields (dimension : ℕ) (domain : Set Spatial) :=
  Lp (Cells dimension) 2 (volume.restrict domain)

def scalarLift (dimension : ℕ) (cell : ℤ) (vector : Values dimension) :
    ℝ →L[ℝ] Cells dimension :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (lp.single 2 cell vector)

def pairingOfMemLp (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) : Fields dimension domain →L[ℂ] ℂ :=
  innerSL ℂ ((scalarLift dimension cell vector).compLp (membership.toLp test))

def compactPairing (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test) :
    Fields dimension domain →L[ℂ] ℂ :=
  pairingOfMemLp dimension domain cell vector test
    (smoothness.continuous.memLp_of_hasCompactSupport compactSupport)

def orderedTestDerivative (rank : ℕ) (word : Fin rank → Fin 2) (test : Spatial → ℝ) :
    Spatial → ℝ :=
  fun point => iteratedFDeriv ℝ rank test point
    (fun position => spatialDirection (word position))

def PairingGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (cell : ℤ) (vector : Values dimension)
    (test : Spatial → ℝ) (membership : MemLp test 2 (volume.restrict domain)),
    (∀ field : Fields dimension domain,
      pairingOfMemLp dimension domain cell vector test membership field =
        ∫ point in domain, test point • inner ℂ vector (field point cell)) ∧
    ‖pairingOfMemLp dimension domain cell vector test membership‖ ≤
      (eLpNorm test 2 (volume.restrict domain)).toReal * ‖vector‖

def DerivativeTestGoal : Prop :=
  ∀ (domain : Set Spatial) (test : Spatial → ℝ),
    ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
      ∀ (rank : ℕ) (word : Fin rank → Fin 2),
        MemLp (orderedTestDerivative rank word test) 2 (volume.restrict domain) ∧
          tsupport (orderedTestDerivative rank word test) ⊆ domain

theorem compactInterfaceConsumer (pairings : PairingGoal) :
    ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
      ∀ (cell : ℤ) (vector : EuclideanSpace ℂ (Fin dimension)) (test : Spatial → ℝ)
        (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test),
        tsupport test ⊆ domain →
        (∀ field : Lp (lp (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2) 2
            (volume.restrict domain),
          compactPairing dimension domain cell vector test smoothness compactSupport field =
            ∫ point in domain, test point • inner ℂ vector (field point cell)) ∧
        ‖compactPairing dimension domain cell vector test smoothness compactSupport‖ ≤
          (eLpNorm test 2 (volume.restrict domain)).toReal * ‖vector‖ := by
  intro dimension domain _openDomain cell vector test smoothness compactSupport _supported
  exact pairings dimension domain cell vector test
    (smoothness.continuous.memLp_of_hasCompactSupport compactSupport)

theorem derivativeInterfaceConsumer (pairings : PairingGoal) (derivatives : DerivativeTestGoal) :
    ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
      ∀ (cell : ℤ) (vector : EuclideanSpace ℂ (Fin dimension)) (test : Spatial → ℝ),
        ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
          ∀ (rank : ℕ) (word : Fin rank → Fin 2),
            ∃ membership : MemLp
                (fun point => iteratedFDeriv ℝ rank test point
                  (fun position => spatialDirection (word position))) 2 (volume.restrict domain),
              tsupport (fun point => iteratedFDeriv ℝ rank test point
                (fun position => spatialDirection (word position))) ⊆ domain ∧
              (∀ field : Lp (lp (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2) 2
                  (volume.restrict domain),
                pairingOfMemLp dimension domain cell vector
                    (fun point => iteratedFDeriv ℝ rank test point
                      (fun position => spatialDirection (word position))) membership field =
                  ∫ point in domain,
                    (iteratedFDeriv ℝ rank test point
                      (fun position => spatialDirection (word position))) •
                        inner ℂ vector (field point cell)) ∧
              ‖pairingOfMemLp dimension domain cell vector
                  (fun point => iteratedFDeriv ℝ rank test point
                    (fun position => spatialDirection (word position))) membership‖ ≤
                (eLpNorm (fun point => iteratedFDeriv ℝ rank test point
                  (fun position => spatialDirection (word position))) 2
                    (volume.restrict domain)).toReal * ‖vector‖ := by
  intro dimension domain _openDomain cell vector test smoothness compactSupport supported rank word
  obtain ⟨membership, derivativeSupport⟩ :=
    derivatives domain test smoothness compactSupport supported rank word
  exact ⟨membership, derivativeSupport,
    pairings dimension domain cell vector (orderedTestDerivative rank word test) membership⟩

end Grad.WeakTesting
