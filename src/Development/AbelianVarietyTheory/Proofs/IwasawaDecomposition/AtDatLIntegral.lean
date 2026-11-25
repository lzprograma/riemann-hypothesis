module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.Mem.Top.Bl

theorem atDat_lIntegral : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LIntegral := fun _ _ _ =>
  StepW.of_all fun _ _ _ _ _ _ _ _ _ _ _ z _ _ _ hG i =>
    ⟨z.geo.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie z.geo.fw hG.latFull i,
      GlobalTheory.RealGeoIn.mkStable_of_rhoGeo z.geo.fw z.geo.pins z.geo.rhoGeo i⟩

end GlobalTheory.Mem.Top.Bl
