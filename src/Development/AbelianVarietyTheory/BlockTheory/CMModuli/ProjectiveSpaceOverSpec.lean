module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

def IsIndEtale {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) : Prop :=
  MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale) (CommRingCat.ofHom φ)

def IsStrictHenselisation {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    (φ : A →+* S) : Prop :=
  HenselianLocalRing S ∧ IsSepClosed (ResidueField S) ∧ IsLocalHom φ ∧ IsIndEtale φ

end GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec
