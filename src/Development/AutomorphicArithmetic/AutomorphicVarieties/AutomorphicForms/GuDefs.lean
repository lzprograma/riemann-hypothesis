module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

namespace UpperTheory.V.Af.Gu

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]


variable (Ω) in
abbrev Par (w : HeightOneSpectrum (𝓞 E)) : Type 1 :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (IrrGL (k := w.adicCompletion E) → WD h) → WD h

abbrev cl {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : IrrGL (k := w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

def ParAt {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (p : Par Ω w) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → Lev.WO ι r (p A h rc)) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := E) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (p A h rc)

theorem ParAt.congr {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {p p' : Par Ω w}
    (H : ParAt ι r w p) (e : ∀ A h rc, IsRec h rc → p A h rc = p' A h rc) : ParAt ι r w p' :=
  fun A h rc hrc => e A h rc hrc ▸ H A h rc hrc

structure Compat {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (p : ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
    (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  ht : HasHT r HT
  par : ∀ w, ParAt ι r w (p w)

def ex (n d k : ℕ) : ℤ := (d : ℤ) - 2 * k - n

def totPar (n : ℕ) {c : ℕ} {a : Fin c → ℕ} (d : Fin c → ℕ) {w : HeightOneSpectrum (𝓞 E)}
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) : Par Ω w := fun _ _ rc =>
  sumList (List.ofFn fun i => sumList (List.ofFn fun k : Fin (d i) => (rc (cl (ρ i))).lpTw ((ex n (d i) k : ℝ) / 2)))

def satTot (w : HeightOneSpectrum (𝓞 E)) {c : ℕ} (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) : Multiset ℂˣ :=
  ∑ i, ∑ k : Fin (d i), (S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))

end Defs

def SumAway : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x x' : WD h),
      IsWDOf ι r x → IsWDOf ι r' x' → IsWDOf ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (x.lpSum x')

def SumRed : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a b : ℕ) (r : Γ →* GL (Fin a) k) (r' : Γ →* GL (Fin b) k), 1 ≤ a → 1 ≤ b →
    ¬ IsIrr (Formalism.MainNotions.SumRepresentations.At.sumRep r r')

def Eta : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ), ∃ (ξ : HChar E) (m : (E →+* ℂ) → ℤ), ξ.IsAlg m ∧
    compNorm E (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ)) = 1

def TwistLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a) (t : ℝ) (w : HeightOneSpectrum (𝓞 E))
    (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∃ σ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E t)).IsLocComp w σ ∧ cl σ = (cl ρ).nu (t : ℂ)

def Strings : Prop :=
  ∀ (n c : ℕ) (d : Fin c → ℕ) (m : Fin c → Multiset ℂ) (lam : DomWeight n),
    ∑ i, GlobalTheory.DefiniteBC.spehInf (d i) (m i) = infOfWeight lam →
    (∀ i (k : Fin (d i)), (m i).Nodup ∧ ∀ z ∈ m i, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j) ∧
      ∑ i, ∑ k : Fin (d i), (m i).map (fun z => -(z + (ex n (d i) k : ℂ) / 2)) =
        (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z

def CompUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₁ →
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₂ → Nonempty (ρ₁.Equiv ρ₂)

def PolOfFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → IsSSRep r →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ,
      FrobEig ι r w (algSat n (normV w) (B.map (·⁻¹))) ∧ FrobEig ι r (Bc.cPl w) (algSat n (normV (Bc.cPl w)) B)) →
    ∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P

def SatLink : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a),
    (∀ (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∀ B, (CG.mk P).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w ρ.ρ B) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    (∀ (a : ℕ) (P : CuspSub E a), P.IsCsd → ∀ B, (CG.mk P).HasSat (Bc.cPl w) B → (CG.mk P).HasSat w (B.map (·⁻¹))) ∧
    ∀ (c : ℕ) (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ),
      satTot w d (fun i => (S i).map (·⁻¹)) = (satTot (Bc.cPl w) d S).map (·⁻¹)

end UpperTheory.V.Af.Gu
