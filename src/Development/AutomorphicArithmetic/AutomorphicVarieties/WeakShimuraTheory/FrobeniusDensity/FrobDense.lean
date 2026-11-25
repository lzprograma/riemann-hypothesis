module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Tw.frobDense :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → Dense {σ : G K Ω | ∃ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), ¬ w.asIdeal ∣ 𝔪 ∧ IsPlaceOver A w ∧ IsFrob A (normV w) σ} := by
  intro K Ω _ _ _ _ _ 𝔪 h𝔪
  have hS : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪}.Finite := Ideal.finite_factors h𝔪
  refine (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := K) (Ω := Ω)
    GlobalTheory.Published.chebotarevDegreeOne' hS).mono ?_
  rintro σ ⟨v, hv, _, B, hB, hσ⟩
  exact ⟨v, B, hv, hB, hσ⟩
