import AKBE14LiteralClosedRadialTranspose
import CUT1Cover

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CompactCutoff
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- An existing compact cutoff can cover every rotation and reflection of a
punctured test support. No radial bump construction is required. -/
theorem originalTest_radialCutoff (test : Spatial → ℝ)
    (supported : tsupport test ⊆ openUnitDisk)
    (away : (0 : Spatial) ∉ tsupport test) :
    ∃ cutoff : Spatial → ℝ, ContDiff ℝ ∞ cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ openUnitDisk \ {(0 : Spatial)} ∧
      ∀ point ∈ tsupport test, ∀ other : Spatial, ‖other‖ = ‖point‖ → cutoff other = 1 := by
  have insideBall : tsupport test ⊆ Metric.ball (0 : Spatial) 1 := by
    intro point membership
    rw [Metric.mem_ball,dist_zero_right]
    exact supported membership
  obtain ⟨upper, upperBounds, upperSupport⟩ :=
    exists_pos_lt_subset_ball zero_lt_one (isClosed_tsupport test) insideBall
  obtain ⟨lower, lowerPositive, lowerSupport⟩ :=
    Metric.isOpen_iff.mp (isClosed_tsupport test).isOpen_compl 0 away
  let annulus : Set Spatial := {point | lower ≤ ‖point‖ ∧ ‖point‖ ≤ upper}
  have annulusClosed : IsClosed annulus :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have annulusCompact : IsCompact annulus :=
    (isCompact_closedBall (0 : Spatial) upper).of_isClosed_subset annulusClosed
      (fun point membership => by simpa only [Metric.mem_closedBall,dist_zero_right] using membership.2)
  have annulusInside : annulus ⊆ openUnitDisk \ {(0 : Spatial)} := by
    intro point membership
    refine ⟨membership.2.trans_lt upperBounds.2, ?_⟩
    intro zeroPoint
    have pointZero : point = 0 := Set.mem_singleton_iff.mp zeroPoint
    have positiveNorm := lowerPositive.trans_le membership.1
    simp only [pointZero,norm_zero,lt_self_iff_false] at positiveNorm
  let cutoff := compactCutoff annulus (openUnitDisk \ {(0 : Spatial)}) annulusCompact
    (openUnitDisk_isOpen.sdiff isClosed_singleton) annulusInside
  refine ⟨cutoff.toFun,cutoff.smooth,cutoff.compact,cutoff.supported,?_⟩
  intro point membership other sameNorm
  apply cutoff.one_on
  change lower ≤ ‖other‖ ∧ ‖other‖ ≤ upper
  rw [sameNorm]
  constructor
  · by_contra below
    have near : point ∈ Metric.ball (0 : Spatial) lower := by
      simpa only [Metric.mem_ball,dist_zero_right] using lt_of_not_ge below
    exact lowerSupport near membership
  · exact (show ‖point‖ < upper by simpa only [Metric.mem_ball,dist_zero_right] using upperSupport membership).le

/-- Localizing on that existing cutoff gives a continuous closed-disk field
which agrees on every orbit needed by the original test transpose. -/
theorem originalTest_continuousLocalization (raw : Spatial → ComplexEuclidean 2)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (test : Spatial → ℝ) (supported : tsupport test ⊆ openUnitDisk)
    (away : (0 : Spatial) ∉ tsupport test) :
    ∃ localized : Spatial → ComplexEuclidean 2, Continuous localized ∧
      ∀ point ∈ tsupport test, ∀ other : Spatial, ‖other‖ = ‖point‖ → localized other = raw other := by
  obtain ⟨cutoff,smooth,_,cutoffSupported,oneOn⟩ := originalTest_radialCutoff test supported away
  refine ⟨fun point => cutoff point • raw point,
    continuous_smul_of_tsupport_subset _ (openUnitDisk_isOpen.sdiff isClosed_singleton)
      cutoff smooth.continuous cutoffSupported raw continuousRaw,?_⟩
  intro point membership other sameNorm
  change cutoff other • raw other = raw other
  rw [oneOn point membership other sameNorm,one_smul]

end Grad.ActualCartesianWeakEquations
