import AKAP2WholePlaneDiskTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2500

open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier

variable (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)

/-- The same actual smooth scalar cutoff on L2. -/
def startupCutoffL2 : StartupL2 3 →L[ℂ] StartupL2 3 :=
  fieldMultiplier 3 openUnitDisk openUnitDisk_isOpen
    (derivativeScalar (compactSymbol 1 openUnitDisk scalar smooth compact) (zeroIndex 1))

def startupCutoffFirst : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  compactJetMultiplier 3 1 openUnitDisk openUnitDisk_isOpen scalar smooth compact
    (fun _ => 0) (constantExponent_antitone 1 0)

theorem startupCutoffFirst_compatible :
    StartupCompatible (startupCutoffL2 scalar smooth compact) (startupCutoffFirst scalar smooth compact) :=
  jetMultiplier_base_apply 3 1 openUnitDisk openUnitDisk_isOpen
    (compactSymbol 1 openUnitDisk scalar smooth compact) (fun _ => 0) (constantExponent_antitone 1 0)

/-- Composition remains abstract during normalization of the transport. -/
def startupLocalizedKernelFor (extension : StartupL2 3 →L[ℂ] FieldL2)
    (cutoff kernel : StartupL2 3 →L[ℂ] StartupL2 3)
    (restriction : FieldL2 →L[ℂ] StartupL2 3) : FieldL2 →L[ℂ] FieldL2 :=
  extension.comp (cutoff.comp (kernel.comp restriction))

theorem startupLocalizedKernelFor_apply (extension : StartupL2 3 →L[ℂ] FieldL2)
    (cutoff kernel : StartupL2 3 →L[ℂ] StartupL2 3)
    (restriction : FieldL2 →L[ℂ] StartupL2 3) (field : FieldL2) :
    startupLocalizedKernelFor extension cutoff kernel restriction field =
      extension (cutoff (kernel (restriction field))) := rfl

theorem startupLocalizedKernelFor_norm (extension : StartupL2 3 →L[ℂ] FieldL2)
    (cutoff kernel : StartupL2 3 →L[ℂ] StartupL2 3)
    (restriction : FieldL2 →L[ℂ] StartupL2 3)
    (extensionBound : ∀ field, ‖extension field‖ ≤ ‖field‖)
    (restrictionBound : ∀ field, ‖restriction field‖ ≤ ‖field‖) :
    ‖startupLocalizedKernelFor extension cutoff kernel restriction‖ ≤ ‖cutoff‖ * ‖kernel‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro field
  rw [startupLocalizedKernelFor_apply]
  calc
    _ ≤ ‖cutoff (kernel (restriction field))‖ := extensionBound _
    _ ≤ ‖cutoff‖ * ‖kernel (restriction field)‖ := cutoff.le_opNorm _
    _ ≤ ‖cutoff‖ * (‖kernel‖ * ‖field‖) :=
      mul_le_mul_of_nonneg_left ((kernel.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (restrictionBound field) (norm_nonneg kernel))) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

/-- Literal restriction, actual disk operator, scalar cutoff and zero
 extension, in this order on the whole-plane L2 carrier. -/
def startupLocalizedKernel (kernel : StartupL2 3 →L[ℂ] StartupL2 3) : FieldL2 →L[ℂ] FieldL2 :=
  startupLocalizedKernelFor startupPlaneExtension (startupCutoffL2 scalar smooth compact) kernel startupPlaneRestriction

theorem startupLocalizedKernel_apply (kernel : StartupL2 3 →L[ℂ] StartupL2 3) (field : FieldL2) :
    startupLocalizedKernel scalar smooth compact kernel field =
      startupPlaneExtension (startupCutoffL2 scalar smooth compact (kernel (startupPlaneRestriction field))) :=
  startupLocalizedKernelFor_apply startupPlaneExtension (startupCutoffL2 scalar smooth compact) kernel startupPlaneRestriction field

theorem startupLocalizedKernel_norm (kernel : StartupL2 3 →L[ℂ] StartupL2 3) :
    ‖startupLocalizedKernel scalar smooth compact kernel‖ ≤ ‖startupCutoffL2 scalar smooth compact‖ * ‖kernel‖ :=
  startupLocalizedKernelFor_norm startupPlaneExtension (startupCutoffL2 scalar smooth compact) kernel startupPlaneRestriction
    (fun field => (startupPlaneExtension_norm field).le) startupPlaneRestriction_norm_le

/-- Remove only the supported-subtype wrapper, keeping every operator abstract. -/
theorem startupCutoffRealizationFor (support : Set Spatial)
    (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2)
    (cutoff : StartupFirst 3 →L[ℂ] StartupFirst 3) (graph : StartupFirst 3)
    (realized : ∃ cut : Grad.WeightedJets.ZeroExtension.supportedJetSubmodule 3 1 openUnitDisk support (fun _ => 0),
      cut.val = cutoff graph ∧ ∃ regular : FieldH1,
        valueInclusion regular = equivalence
          (Grad.WeightedJets.ZeroExtension.fieldExtension CellValues openUnitDisk openUnitDisk_isOpen.measurableSet
            (base 3 1 openUnitDisk (fun _ => 0) cut.val)) ∧ ‖regular‖ = ‖cut‖) :
    ∃ regular : FieldH1,
      valueInclusion regular = startupPlaneExtensionFor equivalence (base 3 1 openUnitDisk (fun _ => 0) (cutoff graph)) ∧
      ‖regular‖ = ‖cutoff graph‖ := by
  obtain ⟨cut, cutSame, regular, represented, normSame⟩ := realized
  refine ⟨regular, ?_, ?_⟩
  · exact represented.trans (congrArg (fun graph : StartupFirst 3 =>
      startupPlaneExtensionFor equivalence (base 3 1 openUnitDisk (fun _ => 0) graph)) cutSame)
  · exact normSame.trans (congrArg (fun graph : StartupFirst 3 => ‖graph‖) cutSame)

/-- The actual cutoff has its SAME whole-plane H1 output before any kernel is inserted. -/
theorem startupCutoff_h1_realization (included : tsupport scalar ⊆ openUnitDisk)
    (graph : StartupFirst 3) :
    ∃ regular : FieldH1,
      valueInclusion regular = startupPlaneExtension
        (base 3 1 openUnitDisk (fun _ => 0) (startupCutoffFirst scalar smooth compact graph)) ∧
      ‖regular‖ = ‖startupCutoffFirst scalar smooth compact graph‖ := by
  have actual := @startupActualCutoff_h1_exists
  change ∃ regular : FieldH1,
    valueInclusion regular = startupPlaneExtensionFor startupWholePlaneField
      (base 3 1 openUnitDisk (fun _ => 0) (startupCutoffFirst scalar smooth compact graph)) ∧
    ‖regular‖ = ‖startupCutoffFirst scalar smooth compact graph‖
  generalize equality : startupWholePlaneField = equivalence at actual ⊢
  clear equality
  as_aux_lemma =>
    exact startupCutoffRealizationFor (tsupport scalar) equivalence
      (startupCutoffFirst scalar smooth compact) graph
      (actual openUnitDisk openUnitDisk_isOpen scalar smooth compact included graph)

/-- Compose abstract SAME base actions before specializing the physical maps. -/
theorem startupLocalizedKernelFor_h1_realization
    (extension : StartupL2 3 →L[ℂ] FieldL2) (restriction : FieldL2 →L[ℂ] StartupL2 3)
    (cutoff kernel : StartupL2 3 →L[ℂ] StartupL2 3)
    (cutoffFine fine : StartupFirst 3 →L[ℂ] StartupFirst 3)
    (cutoffCompatible : StartupCompatible cutoff cutoffFine)
    (compatible : StartupCompatible kernel fine)
    (restricted : ∀ field : FieldH1, ∃ graph : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) graph = restriction (valueInclusion field) ∧ ‖graph‖ ≤ ‖field‖)
    (cutoffRealized : ∀ graph : StartupFirst 3, ∃ regular : FieldH1,
      valueInclusion regular = extension (base 3 1 openUnitDisk (fun _ => 0) (cutoffFine graph)) ∧
      ‖regular‖ = ‖cutoffFine graph‖)
    (field : FieldH1) :
    ∃ output : FieldH1,
      valueInclusion output = startupLocalizedKernelFor extension cutoff kernel restriction (valueInclusion field) ∧
      ‖output‖ ≤ (‖cutoffFine‖ * ‖fine‖) * ‖field‖ := by
  obtain ⟨graph, represented, graphBound⟩ := restricted field
  obtain ⟨regular, regularSame, normSame⟩ := cutoffRealized (fine graph)
  refine ⟨regular, ?_, ?_⟩
  · exact regularSame.trans ((congrArg extension (cutoffCompatible (fine graph))).trans
      ((congrArg (fun value : StartupL2 3 => extension (cutoff value)) (compatible graph)).trans
      (congrArg (fun value : StartupL2 3 => extension (cutoff (kernel value))) represented)))
  · rw [normSame]
    calc
      _ ≤ ‖cutoffFine‖ * ‖fine graph‖ := cutoffFine.le_opNorm (fine graph)
      _ ≤ ‖cutoffFine‖ * (‖fine‖ * ‖field‖) :=
        mul_le_mul_of_nonneg_left ((fine.le_opNorm graph).trans
          (mul_le_mul_of_nonneg_left graphBound (norm_nonneg fine))) (norm_nonneg cutoffFine)
      _ = _ := (mul_assoc _ _ _).symm

/-- The original first-graph operator gives an actual H1 output for the
 SAME localized L2 action with the fixed cutoff norm payment. -/
theorem startupLocalizedKernel_h1_realization
    (included : tsupport scalar ⊆ openUnitDisk)
    (kernel : StartupL2 3 →L[ℂ] StartupL2 3) (fine : StartupFirst 3 →L[ℂ] StartupFirst 3)
    (compatible : StartupCompatible kernel fine) (field : FieldH1) :
    ∃ output : FieldH1,
      valueInclusion output = startupLocalizedKernel scalar smooth compact kernel (valueInclusion field) ∧
      ‖output‖ ≤ (‖startupCutoffFirst scalar smooth compact‖ * ‖fine‖) * ‖field‖ :=
  startupLocalizedKernelFor_h1_realization startupPlaneExtension startupPlaneRestriction
    (startupCutoffL2 scalar smooth compact) kernel (startupCutoffFirst scalar smooth compact) fine
    (startupCutoffFirst_compatible scalar smooth compact) compatible startupH1_diskGraph_exists
    (startupCutoff_h1_realization scalar smooth compact included) field

/-- Keep the input composition abstract when constructing the SAME H1 lift. -/
theorem startupH1_kernel_lift (kernel : FieldL2 →L[ℂ] FieldL2) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (realized : ∀ field : FieldH1, ∃ output : FieldH1,
      valueInclusion output = kernel (valueInclusion field) ∧ ‖output‖ ≤ bound * ‖field‖) :
    ∃ lift : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (lift field) = kernel (valueInclusion field)) ∧ ‖lift‖ ≤ bound :=
  startupH1_bounded_lift (kernel.comp valueInclusion) bound boundNonnegative realized

/-- A genuine bounded H1 realization of the SAME localized kernel, with
 compatibility and the explicit fixed cutoff norm payment. -/
theorem startupLocalizedKernel_h1_exists
    (included : tsupport scalar ⊆ openUnitDisk)
    (kernel : StartupL2 3 →L[ℂ] StartupL2 3) (fine : StartupFirst 3 →L[ℂ] StartupFirst 3)
    (compatible : StartupCompatible kernel fine) :
    ∃ regular : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (regular field) = startupLocalizedKernel scalar smooth compact kernel (valueInclusion field)) ∧
      ‖regular‖ ≤ ‖startupCutoffFirst scalar smooth compact‖ * ‖fine‖ :=
  startupH1_kernel_lift (startupLocalizedKernel scalar smooth compact kernel)
    (‖startupCutoffFirst scalar smooth compact‖ * ‖fine‖) (mul_nonneg (norm_nonneg (startupCutoffFirst scalar smooth compact)) (norm_nonneg fine))
    (startupLocalizedKernel_h1_realization scalar smooth compact included kernel fine compatible)

end Grad.CartesianStartup
