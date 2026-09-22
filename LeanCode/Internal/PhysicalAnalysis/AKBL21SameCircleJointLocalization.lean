import AKBL20ComplementFourierCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.CompactCutoff
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- One existing spatial cutoff localizes the whole axial family on the
same circle. This is a continuous closed representative, with no imposed
axis values and no change to the original source on the target orbit. -/
theorem startupJointCircle_continuousLocalization {dimension : ℕ}
    (raw : ℝ × Spatial → PhysicalValue dimension)
    (continuousRaw : ContinuousOn raw {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}})
    (point : Spatial) (positive : 0 < ‖point‖) (inside : ‖point‖ < 1) :
    ∃ localized : ℝ → C(ClosedDisk,PhysicalValue dimension), Continuous localized ∧
      ∀ angle (other : ClosedDisk), ‖other.val‖ = ‖point‖ → localized angle other = raw (angle,other.val) := by
  let circle := Metric.sphere (0 : Spatial) ‖point‖
  have included : circle ⊆ openUnitDisk \ {(0 : Spatial)} := by
    intro other membership
    have sameNorm : ‖other‖ = ‖point‖ := by simpa only [circle,Metric.mem_sphere,dist_zero_right] using membership
    refine ⟨sameNorm.trans_lt inside,?_⟩
    intro zeroPoint
    have otherZero : other = 0 := Set.mem_singleton_iff.mp zeroPoint
    rw [otherZero,norm_zero] at sameNorm
    exact (ne_of_gt positive) sameNorm.symm
  let cutoff := compactCutoff circle (openUnitDisk \ {(0 : Spatial)}) (isCompact_sphere 0 ‖point‖)
    (openUnitDisk_isOpen.sdiff isClosed_singleton) included
  let localRaw : ℝ × Spatial → PhysicalValue dimension := fun pair => cutoff.toFun pair.2 • raw pair
  have openDomain : IsOpen {pair : ℝ × Spatial | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} :=
    (openUnitDisk_isOpen.sdiff isClosed_singleton).preimage continuous_snd
  have continuousLocal : Continuous localRaw := by
    apply continuous_iff_continuousAt.mpr
    intro pair
    by_cases supported : pair.2 ∈ tsupport cutoff.toFun
    · have insidePair : pair ∈ {pair : ℝ × Spatial | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} := cutoff.supported supported
      exact (cutoff.smooth.continuous.comp continuous_snd).continuousAt.smul
        (continuousRaw.continuousAt (openDomain.mem_nhds insidePair))
    · have near : ∀ᶠ query : ℝ × Spatial in 𝓝 pair, query.2 ∉ tsupport cutoff.toFun :=
        continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport cutoff.toFun).isOpen_compl.mem_nhds supported)
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [near] with query away
      change localRaw query = (0 : PhysicalValue dimension)
      simp only [localRaw,image_eq_zero_of_notMem_tsupport away,zero_smul]
  let localized : ℝ → C(ClosedDisk,PhysicalValue dimension) := fun angle =>
    ⟨fun other => localRaw (angle,other.val),continuousLocal.comp (continuous_const.prodMk continuous_subtype_val)⟩
  refine ⟨localized,?_,?_⟩
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuousLocal.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  · intro angle other sameNorm
    change cutoff.toFun other.val • raw (angle,other.val) = raw (angle,other.val)
    rw [cutoff.one_on (by simpa only [circle,Metric.mem_sphere,dist_zero_right] using sameNorm),one_smul]

end Grad.CartesianStartup
