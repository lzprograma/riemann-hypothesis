module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical



theorem _root_.GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)}, PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → x ∈ F.lat → IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) := by
  first | exact @GlobalTheory.LatHalfInt.frMap_int_of_mem_lat
