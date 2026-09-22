import ANH1UnweightedDisk

noncomputable section

open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Envelope Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Algebra

theorem unweightedJet (cell : ℤ) (field : ClosedJet 1) :
    apWeightedJet 0 0 1 cell field = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [apWeightedJet_value]
  simp [originalWeight, physicalWeight, Grad.AnalyticWeights.weight,
    Grad.AnalyticWeights.phase]

theorem diskCoordinate_core (index : DerivativeIndex 1) (field : ClosedJet 1) :
    diskCoordinate index (diskCoreInto field) =
      closedDerivativeL2 (derivativeMultiIndex index) field := by
  change apUnscaledCoordinate 1 0 0 1 0 index
    (apFiniteInto 1 0 0 1 (Finsupp.single 0 field)) = _
  rw [apUnscaledCoordinate_core, Finsupp.single_eq_same, unweightedJet]

theorem diskCore_norm_sq (field : ClosedJet 1) :
    ‖diskCoreInto field‖ ^ 2 =
      ∑ index : DerivativeIndex 1, ‖closedDerivativeL2 (derivativeMultiIndex index) field‖ ^ 2 := by
  change ‖apFiniteEmbed (grade := 1) 1 0 0 1 (Finsupp.single 0 field)‖ ^ 2 = _
  rw [apFiniteEmbed_single]
  change ‖(lp.single 2 0 (apRowLinear (grade := 1) 1 0 0 1 0 field) : APAmbient 1 1)‖ ^ 2 = _
  rw [lp.norm_single, apRowLinear_norm_sq, unweightedJet]
  · simp [scaledCellWeight]
  · norm_num

/-- Remove precisely -2,-1,0,1,2 before taking the full-disk H1 closure. -/
def highDiskCore : ClosedJet 1 →ₗ[ℂ] diskGrade :=
  diskCoreInto.comp (excludedAngularJetLinear 1 lowAngularModes)

def highDiskGrade : Submodule ℂ diskGrade := highDiskCore.range.topologicalClosure

instance highDiskGrade_complete : CompleteSpace highDiskGrade := by
  unfold highDiskGrade
  infer_instance

def highDiskCoreInto : ClosedJet 1 →ₗ[ℂ] highDiskGrade :=
  highDiskCore.codRestrict _ (fun field =>
    Submodule.le_topologicalClosure _ ⟨field, rfl⟩)

theorem highDiskCoreInto_denseRange : DenseRange highDiskCoreInto := by
  have dense : DenseRange (Set.inclusion (Submodule.le_topologicalClosure highDiskCore.range)) := by
    apply (denseRange_inclusion_iff _).2
    intro point member
    exact member
  apply dense.mono
  rintro _ ⟨⟨point, field, equality⟩, rfl⟩
  exact ⟨field, Subtype.ext equality⟩

def highDiskBulk : highDiskGrade →L[ℂ] DiskL2 1 :=
  diskBulk.comp highDiskGrade.subtypeL

theorem highDiskBulk_injective : Function.Injective highDiskBulk := by
  intro first second equality
  apply Subtype.ext
  exact diskBulk_injective equality

theorem highDiskCore_norm_sq (field : ClosedJet 1) :
    ‖highDiskCoreInto field‖ ^ 2 =
      ∑ index : DerivativeIndex 1,
        ‖closedDerivativeL2 (derivativeMultiIndex index)
          (excludedAngularJet lowAngularModes field)‖ ^ 2 :=
  diskCore_norm_sq _

end Grad.CircularHighWeak
