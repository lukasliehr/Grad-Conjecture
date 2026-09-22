import AKAG4SupportedFirstGraphH1
import AKAG7CompactExtensionSupport

noncomputable section

set_option maxHeartbeats 400000

open MeasureTheory
open Grad.PDEBootstrap
open scoped ContDiff

namespace Grad.CartesianStartup

open Grad.WeightedJets Grad.WeightedJets.ZeroExtension

/-- Actual compact first graphs have SAME zero-extended H1 realizations with no norm loss. -/
theorem startupCompactFirst_h1_exists (domain support : Set Spatial)
    (openDomain : IsOpen domain) (compact : IsCompact support) (included : support ⊆ domain)
    (field : supportedJetSubmodule 3 1 domain support (fun _ => 0)) :
    ∃ regular : FieldH1,
      valueInclusion regular = startupWholePlaneField
        (fieldExtension CellValues domain openDomain.measurableSet
          (base 3 1 domain (fun _ => 0) field.val)) ∧
      ‖regular‖ = ‖field‖ := by
  let extended : supportedJetSubmodule 3 1 Set.univ support (fun _ => 0) :=
    ⟨compactExtension 3 1 domain support compact openDomain included (fun _ => 0) field,
      startupExtendJet_supported 3 1 domain support openDomain.measurableSet
        (compactLocalizer domain support compact openDomain included) (fun _ => 0) field.val field.property⟩
  obtain ⟨regular, represented, _coordinates, sameNorm⟩ := startupSupportedFirst_h1_exists_norm
    (compactLocalizer Set.univ support compact isOpen_univ (Set.subset_univ support)) extended
  refine ⟨regular, ?_, sameNorm.trans ?_⟩
  · exact represented.trans (congrArg startupWholePlaneField
      (extendJet_base 3 1 domain support openDomain.measurableSet
        (compactLocalizer domain support compact openDomain included) (fun _ => 0) field.val field.property))
  · exact compactExtension_norm 3 1 domain support compact openDomain included (fun _ => 0) field

/-- The actual scalar cutoff is retained in its native supported graph carrier.
 Its SAME zero-extended H1 realization has exactly that inherited graph norm. -/
theorem startupActualCutoff_h1_exists (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ domain) (field : GraphGrade 3 1 0 domain) :
    ∃ cut : supportedJetSubmodule 3 1 domain (tsupport scalar) (fun _ => 0),
      cut.val = SpatialMultiplier.compactJetMultiplier 3 1 domain openDomain scalar smooth compact
        (fun _ => 0) (by intro _ _ _; exact le_rfl) field ∧
      ∃ regular : FieldH1,
        valueInclusion regular = startupWholePlaneField
          (fieldExtension CellValues domain openDomain.measurableSet
            (base 3 1 domain (fun _ => 0) cut.val)) ∧
        ‖regular‖ = ‖cut‖ := by
  let multiplied := SpatialMultiplier.compactJetMultiplier 3 1 domain openDomain scalar smooth compact
    (fun _ => 0) (by intro _ _ _; exact le_rfl) field
  have supported : TupleSupported 3 1 domain (tsupport scalar) multiplied.val :=
    compactJetMultiplier_supported 3 1 domain openDomain scalar smooth compact
      (fun _ => 0) (by intro _ _ _; exact le_rfl) field
  let cut : supportedJetSubmodule 3 1 domain (tsupport scalar) (fun _ => 0) := ⟨multiplied, supported⟩
  exact ⟨cut, rfl, startupCompactFirst_h1_exists domain (tsupport scalar) openDomain compact included cut⟩

end Grad.CartesianStartup
