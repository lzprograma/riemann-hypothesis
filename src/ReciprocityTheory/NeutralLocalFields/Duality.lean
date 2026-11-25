module

public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation

namespace Neutral.B1

section CohA

set_option linter.unusedVariables false

noncomputable section


variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

section ContMaps

variable (R M)

abbrev contMaps (X : Type*) [TopologicalSpace X] : Submodule R (X → M) :=
  ReciprocityTheory.Gal.contMaps R M X

variable {R M}

end ContMaps

abbrev ContAction (rho : Representation R G M) : Prop :=
  ReciprocityTheory.Gal.ContAction rho

variable (rho : Representation R G M)

abbrev H0 : Submodule R M := ReciprocityTheory.Gal.H0 rho

theorem mem_riemannRochSpace_iff_regularAt_everywhere (m : M) : m ∈ H0 rho ↔ ∀ g, rho g m = m :=
  ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere rho m

abbrev Z1 : Submodule R (G → M) := ReciprocityTheory.Gal.Z1 rho

abbrev d0 : M →ₗ[R] (G → M) := ReciprocityTheory.Gal.d0 rho

abbrev Bd1 : Submodule R (G → M) := ReciprocityTheory.Gal.B1 rho

theorem mem_contCoboundaries1 (f : G → M) : f ∈ Bd1 rho ↔ ∃ m, ∀ g, f g = rho g m - m :=
  ReciprocityTheory.Gal.mem_coboundaries1 rho f

abbrev H1 := ReciprocityTheory.Gal.H1 rho

abbrev Z2 : Submodule R (G × G → M) := ReciprocityTheory.Gal.Z2 rho

abbrev d1 : (G → M) →ₗ[R] (G × G → M) := ReciprocityTheory.Gal.d1 rho

abbrev Bd2 : Submodule R (G × G → M) := ReciprocityTheory.Gal.B2 rho

theorem mem_contCoboundaries2 (f : G × G → M) :
    f ∈ Bd2 rho ↔ ∃ c : G → M, Continuous c ∧ d1 rho c = f :=
  ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem rho f

abbrev H2 := ReciprocityTheory.Gal.H2 rho

abbrev Cn (rho : Representation R G M) (n : ℕ) : Submodule R ((Fin n → G) → M) :=
  ReciprocityTheory.Gal.Cn rho n

abbrev dn (n : ℕ) : ((Fin n → G) → M) →ₗ[R] ((Fin (n + 1) → G) → M) :=
  ReciprocityTheory.Gal.dn rho n

abbrev Zn (n : ℕ) : Submodule R ((Fin n → G) → M) := ReciprocityTheory.Gal.Zn rho n

abbrev Bn (n : ℕ) : Submodule R ((Fin n → G) → M) := ReciprocityTheory.Gal.Bn rho n

abbrev Hn (n : ℕ) := ReciprocityTheory.Gal.Hn rho n

section Restriction

variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)

variable (hphi : Continuous phi)
include hphi

abbrev restrictCocycles1 : Z1 rho →ₗ[R] Z1 (rho.comp phi) :=
  ReciprocityTheory.Gal.restrictCocycles1 rho phi hphi

abbrev resH1 : H1 rho →ₗ[R] H1 (rho.comp phi) :=
  ReciprocityTheory.Gal.resH1 rho phi hphi

abbrev restrictCocycles2 : Z2 rho →ₗ[R] Z2 (rho.comp phi) :=
  ReciprocityTheory.Gal.restrictCocycles2 rho phi hphi

abbrev resH2 : H2 rho →ₗ[R] H2 (rho.comp phi) :=
  ReciprocityTheory.Gal.resH2 rho phi hphi

end Restriction

section Tate

def normEnd [Finite G] : Module.End R M := ∑ᶠ g : G, rho g

def normSub [Finite G] : Submodule R (H0 rho) := (LinearMap.range (normEnd rho)).comap (H0 rho).subtype

abbrev tateH0 [Finite G] := H0 rho ⧸ normSub rho

end Tate

end

end CohA

section Coh

noncomputable section


variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

variable (rho : Representation R G M)

section Local

variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))

abbrev LocCond := ∀ i, Submodule R (H1 (rho.comp (phi i)))

def Sel (L : LocCond rho phi) : Submodule R (H1 rho) :=
  ⨅ i, (L i).comap (resH1 rho (phi i) (hphi i))

end Local

section Inertia

variable {D : Type*} [Group D] [TopologicalSpace D] (rhoD : Representation R D M)
  (J : Subgroup D)

def H1ur : Submodule R (H1 rhoD) :=
  LinearMap.ker (resH1 rhoD J.subtype continuous_subtype_val)

end Inertia

end

end Coh

instance (priority := 100) continuousConstSMul_of_discrete {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

section Coeff

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ]
  {M : Type*} [AddCommGroup M] [Module R M]

def charRep (χ : Γ →* Rˣ) : Representation R Γ R where
  toFun g := ((χ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

@[simp] theorem charRep_apply (χ : Γ →* Rˣ) (g : Γ) (x : R) :
    charRep χ g x = ((χ g : Rˣ) : R) * x := rfl


end Coeff

section Cyc

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
  (n : ℕ) [NeZero n]

def cycN : (L ≃ₐ[K] L) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L n)).comp
    (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L)


end Cyc

section Local

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

abbrev GK : Type := PadicAlgCl p ≃ₐ[K] PadicAlgCl p

def inertiaSet : Set (GK p K) := {σ | ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}

def inertiaK : Subgroup (GK p K) := Subgroup.closure (inertiaSet p K)

abbrev cycK (n : ℕ) [NeZero n] : GK p K →* (ZMod n)ˣ := cycN K (PadicAlgCl p) n

variable {p K}


variable (p) in
def KbarMult : Type := Additive (PadicAlgCl p)ˣ

instance : AddCommGroup (KbarMult p) := inferInstanceAs (AddCommGroup (Additive (PadicAlgCl p)ˣ))
instance : TopologicalSpace (KbarMult p) := ⊥
instance : DiscreteTopology (KbarMult p) := ⟨rfl⟩


variable (p K) in
def kbarRep : Representation ℤ (GK p K) (KbarMult p) where
  toFun σ := AddMonoidHom.toIntLinearMap
    (MonoidHom.toAdditive (Units.map (σ : PadicAlgCl p →* PadicAlgCl p)))
  map_one' := by
    apply LinearMap.ext; intro x
    apply Units.ext
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext; intro x
    apply Units.ext
    rfl

abbrev QZ : Type := ℚ ⧸ (Int.castAddHom ℚ).range

end Local

def LocalInvariantIsomorphism : Prop := ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
  FiniteDimensional ℚ_[p] K →
    Nonempty (H2 (kbarRep p K) ≃ₗ[ℤ] QZ) ∧
    ∀ (n : ℕ) [NeZero n], Nonempty (H2 (charRep (cycK p K n)) ≃ₗ[ZMod n] ZMod n)

section Global

open Formalism.ConjugateSelfDual (G IsPlaceOver Inertia)

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

variable (F) in
def DecInf (j : Ω →+* ℂ) : Subgroup (G F Ω) where
  carrier := {σ | (∀ x, j (σ x) = j x) ∨ ∀ x, j (σ x) = starRingEnd ℂ (j x)}
  one_mem' := Or.inl fun x => rfl
  mul_mem' := by
    rintro σ τ (hσ | hσ) (hτ | hτ)
    · exact Or.inl fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inr fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inr fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ]
    · exact Or.inl fun x => by simp only [AlgEquiv.mul_apply, hσ, hτ, Complex.conj_conj]
  inv_mem' := by
    rintro σ (hσ | hσ)
    · refine Or.inl fun x => ?_
      have := hσ (σ⁻¹ x)
      rw [show σ (σ⁻¹ x) = x from by simp] at this
      exact this.symm
    · refine Or.inr fun x => ?_
      have := hσ (σ⁻¹ x)
      rw [show σ (σ⁻¹ x) = x from by simp] at this
      rw [this, Complex.conj_conj]

theorem mem_DecInf (j : Ω →+* ℂ) (σ : G F Ω) :
    σ ∈ DecInf F j ↔ (∀ x, j (σ x) = j x) ∨ ∀ x, j (σ x) = starRingEnd ℂ (j x) := Iff.rfl

instance finite_DecInf (j : Ω →+* ℂ) : Finite (DecInf F j) := by
  classical
  refine Finite.of_injective (fun σ : DecInf F j => decide (∀ x, j (σ.1 x) = j x)) ?_
  intro σ τ h
  have hiff : (∀ x, j (σ.1 x) = j x) ↔ ∀ x, j (τ.1 x) = j x := by simpa using h
  have hσ := (mem_DecInf j σ.1).1 σ.2
  have hτ := (mem_DecInf j τ.1).1 τ.2
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply j.injective
  by_cases h1 : ∀ x, j (σ.1 x) = j x
  · rw [h1 x, hiff.1 h1 x]
  · have h2 : ¬ ∀ x, j (τ.1 x) = j x := fun h' => h1 (hiff.2 h')
    rw [hσ.resolve_left h1 x, hτ.resolve_left h2 x]

section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))


variable (Ω) in
def NS : Subgroup (G F Ω) :=
  (Subgroup.normalClosure
    (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := F) A)
    ).topologicalClosure

instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _


variable (Ω) in
abbrev GS := G F Ω ⧸ NS Ω S


variable (Ω) in
def toGS : G F Ω →* GS Ω S := QuotientGroup.mk' (NS Ω S)

variable (Ω) in
theorem continuous_toGS : Continuous (toGS Ω S) := QuotientGroup.continuous_mk

end unram


variable (F Ω) in
def cycG [IsAlgClosure F Ω] (n : ℕ) [NeZero n] : G F Ω →* (ZMod n)ˣ :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  cycN F Ω n


variable (F Ω) in
structure GData [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) [NeZero n] where

  A : S → ValuationSubring Ω
  hA : ∀ v, IsPlaceOver (A v) v.1

  J : InfinitePlace F → (Ω →+* ℂ)
  hJ : ∀ w, InfinitePlace.mk ((J w).comp (algebraMap F Ω)) = w

  chi : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod n)ˣ
  hchi : chi.comp (toGS Ω _) = cycG F Ω n

variable [IsAlgClosure F Ω] {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n]

def locGrp (D : GData F Ω S n) : S ⊕ InfinitePlace F → Subgroup (G F Ω) :=
  Sum.elim (fun v => (D.A v).decompositionSubgroup F) (fun w => DecInf F (D.J w))

def locHom (D : GData F Ω S n) (i : S ⊕ InfinitePlace F) :
    locGrp D i →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
  (toGS Ω _).comp (locGrp D i).subtype

theorem continuous_locHom (D : GData F Ω S n) (i : S ⊕ InfinitePlace F) :
    Continuous (locHom D i) :=
  (continuous_toGS Ω _).comp continuous_subtype_val

abbrev locF (D : GData F Ω S n) (v : S) := locHom D (Sum.inl v)

theorem continuous_locF (D : GData F Ω S n) (v : S) : Continuous (locF D v) :=
  continuous_locHom D _

abbrev locI (D : GData F Ω S n) (w : InfinitePlace F) := locHom D (Sum.inr w)

instance finite_locGrp_inr (D : GData F Ω S n) (w : InfinitePlace F) :
    Finite (locGrp D (Sum.inr w)) :=
  inferInstanceAs (Finite (DecInf F (D.J w)))

end Global

section PTMaps

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
  {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

def PTCase (F : Type) [Field F] [NumberField F] (n : ℕ) : Prop :=
  Odd n ∨ InfinitePlace.nrRealPlaces F = 0

def Recip (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n) : Prop :=
  ∀ c : H2 (charRep D.chi),
    ∑ v : S, inv v (resH2 (charRep D.chi) (locF D v) (continuous_locF D v) c) = 0

variable (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n)

end PTMaps

section PTMapsAll

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
  {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

abbrev P0 := (∀ v : S, H0 (rho.comp (locF D v))) × (∀ w : InfinitePlace F, tateH0 (rho.comp (locI D w)))

variable (inv : ∀ i : S ⊕ InfinitePlace F, H2 ((charRep D.chi).comp (locHom D i)) →ₗ[ZMod n] ZMod n)

end PTMapsAll

section LubinTate

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def intK : Subring (PadicAlgCl p) where
  carrier := {x | x ∈ K ∧ ‖x‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    rw [norm_mul]
    exact mul_le_one₀ ha' (norm_nonneg _) hb'
  one_mem' := ⟨K.one_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨K.add_mem ha hb, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha' hb')⟩
  zero_mem' := ⟨K.zero_mem, by simp⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨K.neg_mem ha, by rwa [norm_neg]⟩

abbrev OK : Type := intK p K

variable {p K}

def IsUnif (π : OK p K) : Prop :=
  ‖(π : PadicAlgCl p)‖ < 1 ∧ ∀ x : OK p K, ‖(x : PadicAlgCl p)‖ < 1 → ∃ y : OK p K, x = π * y

def resCard (π : OK p K) : ℕ := Nat.card (OK p K ⧸ Ideal.span {π})

end LubinTate

section Division

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def ltPoly (π : OK p K) : Polynomial (PadicAlgCl p) :=
  Polynomial.X ^ resCard π + Polynomial.C (π : PadicAlgCl p) * Polynomial.X

end Division


section Hecke

variable (K : Type) [Field K] [NumberField K]

variable {K}

def infComp (x : Ideles K) (v : InfinitePlace K) : v.Completion := (x : AdeleRing (𝓞 K) K).1 v

def finComp (x : Ideles K) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  (x : AdeleRing (𝓞 K) K).2 v

def embC (σ : K →+* ℂ) : (InfinitePlace.mk σ).Completion →+* ℂ := by
  classical
  exact if σ = (InfinitePlace.mk σ).embedding then InfinitePlace.Completion.extensionEmbedding _
    else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _)

end Hecke

end Neutral.B1
