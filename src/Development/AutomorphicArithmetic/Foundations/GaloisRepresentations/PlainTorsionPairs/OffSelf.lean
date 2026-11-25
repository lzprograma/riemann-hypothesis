module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th

namespace UpperTheory.Gal.projectedFormsSystemPart

theorem la_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A A' : ValuationSubring Ω} {w w' : W.Plc F} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (e : A = A')
    (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (ψ' : Fin n → Dec (F := F) A' →* (Qbar l)ˣ)
    (hψ : ∀ j (g : Dec (F := F) A) (g' : Dec (F := F) A'), (g : G F Ω) = (g' : G F Ω) → ψ j g = ψ' j g') (wt : Fin n → W.Emb l w → ℤ)
    (hm : ∀ τ, StrictMono fun j => wt j τ) (hl : ∀ j, W.IsLocAlg h (ψ j) (wt j)) :
    ∃ wt' : Fin n → W.Emb l w' → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧ ∀ j, W.IsLocAlg h' (ψ' j) (wt' j) := by
  subst e
  obtain rfl : w = w' := IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))
  obtain rfl : ψ = ψ' := funext fun j => MonoidHom.ext fun g => hψ j g g rfl
  exact ⟨wt, hm, hl⟩

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}

@[reducible] def setS (R : CReal k c₁ f 3 ka) (S : Fr.Space c₁.O (Φ.ext f) 3) : CReal k c₁ f 3 ka := { R with S := S }

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem kap (R : CReal k c₁ f 3 ka) (g : G L Ω) : R.K.κA (Qbar l) (R.V.pr g) = ka g := Units.ext (R.κ_pr g)

theorem psi_j (ρ : Fr.NRep (Φ.ext f) 3 (Qbar l)) {u u' : Φ.V} (e : u = u') (j : Fin 3) (a : Φ.Gv u) (a' : Φ.Gv u')
    (h : (k.j u a).1 = (k.j u' a').1) : ρ.ψ u j a = ρ.ψ u' j a' := by
  subst e
  rw [k.j_inj u (Subtype.ext h)]

end

end UpperTheory.Gal.projectedFormsSystemPart
