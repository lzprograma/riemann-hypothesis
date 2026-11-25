module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PhiCondOfFiniteH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.phiDec :
    LocalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → PhiCond (Dec (F := F) A) l := by
  intro hLF l hl F Ω _ _ _ _ _ A v hA
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (Dec (F := F) A) (l ^ 1) := UpperTheory.V.Alg.phiCond_of_finite_H1 (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
    obtain ⟨-, f1, -⟩ := hLF F Ω l 1 M A ρ v one_pos hA hρ
    exact f1
  rwa [pow_one] at key
