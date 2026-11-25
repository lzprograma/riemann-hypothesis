module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjectiveStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_isLocallySurjective : ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q),
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f →
    QuasiIso ((chains R).map (show ((Arrow.mk f).cechNerve : Spc) ⟶ disc.obj Q from
      (Arrow.mk f).augmentedCechNerve.hom)) := by
  intro R _ P Q f hf
  exact _root_.GlobalTheory.EtC.quasiIso_chains_cech_of_locSurj R f (fun U y => ⟨Presheaf.imageSieve f y, hf.imageSieve_mem y, fun V g hg => hg⟩)

end GlobalTheory.EtC
