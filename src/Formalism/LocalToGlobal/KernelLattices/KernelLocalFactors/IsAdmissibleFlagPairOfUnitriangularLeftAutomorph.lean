module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport
public import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegralsCongrFact

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.L2.Th1.H
open Formalism.MainNotions
open Formalism.MainNotions.GlobalTheoryTheory.Inhab (mem_stdL single_mem_stdL)

private def KapChoice.toCd {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) :
    Cd.KapChoice (D := Car.ofRec D) γ₀ :=
  ⟨k.pp, k.pp_over, k.pi, k.pi_gen, k.gaP, k.gaP_at, k.rt, k.rt_pow⟩

private def Base.toCd {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) :
    Cd.Base (Car.ofRec D) cc δ :=
  ⟨B.L, B.lat, B.ω₀, B.t0, B.γ₀, B.gC, B.gC_spec, B.kc.toCd⟩

theorem formV_apply (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) (z w : n → Fin N' → Fin N → ℂ) :
    formV A n N N' z w = (∑ τ, ∑ i, ∑ j, z τ i j * conj (w τ i j)) / (A : ℂ) := rfl

theorem formV_herm (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (formV A n N N') :=
  Cd.formV_herm A n N N'

theorem Hf_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (z w : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Hf D T z w = formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z w := rfl

theorem U_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.U D T x G = opU (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') x G := rfl

theorem Iop_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.Iop D T La₁ La₂ G = inter (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La₁ La₂ G := rfl

theorem mem_ThSp_of (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La' : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ)
    (h : G ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La') :
    G ∈ TaylorLogMetric.ThSp D T La' :=
  ⟨fun z => (h.1 z (Set.mem_univ z)).differentiableAt, fun x hx z => h.2 x hx z⟩

section Gen

variable (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) {n : Type} [Fintype n] [DecidableEq n]
  (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (κ : ℂ)

theorem thM_spec (h : StdOK L ω₀ c ΛM g) (hκ : κ ≠ 0) : IsThM L ω₀ c ΛM g κ (thM L ω₀ c ΛM g κ) :=
  Cd.thM_spec L ω₀ c ΛM g κ h hκ

theorem isThM_ne_zero (h : StdOK L ω₀ c ΛM g) (hκ : κ ≠ 0) {θ : (n → ℂ) → ℂ} (hθ : IsThM L ω₀ c ΛM g κ θ) :
    θ ≠ 0 :=
  Cd.isThM_ne_zero L ω₀ c ΛM g κ h hκ hθ

theorem isThM_spans (h : StdOK L ω₀ c ΛM g) (hκ : κ ≠ 0) {θ : (n → ℂ) → ℂ} (hθ : IsThM L ω₀ c ΛM g κ θ) :
    ∀ F ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ :=
  ((_root_.Formalism.L2.Th1.H.thetaVector L ω₀ n _ ΛM _ _ g h κ hκ).2 θ hθ.1 hθ.2).2.2

end Gen

theorem tensPow_ne_zero {n : Type} [Fintype n] {θ : (n → ℂ) → ℂ} (hθ : θ ≠ 0) (N N' : ℕ) :
    tensPow θ N N' ≠ 0 :=
  Cd.tensPow_ne_zero hθ N N'

section Tens

variable {n : Type} [Fintype n] [DecidableEq n]

theorem matH_hOne (L : PeriodPair) (z w : n → ℂ) :
    matH (hOne L n) z w = (∑ τ, z τ * conj (w τ)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) :=
  Cd.matH_hOne L z w

theorem formV_sum (L : PeriodPair) (N N' : ℕ) (z w : n → Fin N' → Fin N → ℂ) :
    formV (Formalism.L2.Th1.F.area L) n N N' z w
      = ∑ i, ∑ j, matH (hOne L n) (fun τ => z τ i j) (fun τ => w τ i j) :=
  Cd.formV_sum L N N' z w

theorem opU_tensPow (L : PeriodPair) (N N' : ℕ) (θ : (n → ℂ) → ℂ) (x z : n → Fin N' → Fin N → ℂ) :
    opU (formV (Formalism.L2.Th1.F.area L) n N N') x (tensPow θ N N') z
      = ∏ i, ∏ j, opU (matH (hOne L n)) (fun τ => x τ i j) θ (fun τ => z τ i j) :=
  Cd.opU_tensPow L N N' θ x z

theorem alphaQ_tensPow (c : ℝ) (L : PeriodPair) (N N' : ℕ) (x : n → Fin N' → Fin N → ℂ) :
    alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N') x
      = ∏ i, ∏ j, alphaQ c (matH (hOne L n)) (fun τ => x τ i j) :=
  Cd.alphaQ_tensPow c L N N' x

def entry (n : Type) (N N' : ℕ) (i : Fin N') (j : Fin N) : (n → Fin N' → Fin N → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun τ =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => Fin N' → Fin N → ℂ) τ))

theorem tensPow_mem (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {θ : (n → ℂ) → ℂ}
    (hθ : θ ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM) (N N' : ℕ) :
    tensPow θ N N' ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N')
      (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N')) (powLat ΛM N N') :=
  Cd.tensPow_mem c L ΛM hθ N N'

end Tens

theorem Th_congr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Sesq V) (α α' : V → ℂ) (Λ : AddSubgroup V)
    (h : ∀ x ∈ Λ, α x = α' x) {F : V → ℂ} (hF : F ∈ Formalism.L2.Th1.H.Th H α Λ) : F ∈ Formalism.L2.Th1.H.Th H α' Λ :=
  Cd.Th_congr H α α' Λ h hF

theorem al_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') (m : ℤ)
    (h : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D T x x).re = (m : ℝ)) :
    TaylorLogMetric.al D T x = alphaQ (Real.sqrt D.host.d / 2) (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') x :=
  Cd.al_eq (Car.ofRec D) ⟨T.emb, T.abelian₂⟩ x m h

section Kap

variable {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀)

theorem classNumber_ne (D : D7) : classNumber D.host.K ≠ 0 := Cd.classNumber_ne (Car.ofRec D)

theorem KapChoice.pi_ne_zero (p : ℕ) (hp : p.Prime) (hs : SplitK D p) : k.pi p ≠ 0 :=
  k.toCd.pi_ne_zero p hp hs

theorem KapChoice.rt_ne_zero (p : ℕ) (hp : p.Prime) (hs : SplitK D p) : k.rt p ≠ 0 :=
  k.toCd.rt_ne_zero p hp hs

theorem KapChoice.kappa_ne_zero : k.kappa ≠ 0 :=
  k.toCd.kappa_ne_zero

end Kap

alias inter_zero := _root_.Formalism.L2.Th1.H.Inv.inter_zero

theorem inter_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (Λ₁ Λ₂ : AddSubgroup V)
    (α : V → ℂ) (s₁ : IsSelfDual H Λ₁) (s₂ : IsSelfDual H Λ₂) (c₁ : IsSemiChar H Λ₁ α) (c₂ : IsSemiChar H Λ₂ α)
    (i₁ : relIdx Λ₁ Λ₂ ≠ 0) (i₂ : relIdx Λ₂ Λ₁ ≠ 0) {F : V → ℂ} (hF : F ∈ fixedBy H α Λ₁) (h0 : F ≠ 0) :
    inter H α Λ₁ Λ₂ F ≠ 0 := by
  intro h
  apply h0
  funext z
  have := _root_.Formalism.L2.Th1.H.interInv V H hH Λ₁ Λ₂ α s₁ s₂ c₁ c₂ i₁ i₂ F hF z
  rw [h, inter_zero] at this
  exact this.symm

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem kappa_ne_zero : B.kappa ≠ 0 := B.toCd.kappa_ne_zero

theorem thMM_spec (h : B.StdOK) : B.IsThMM B.thMM := B.toCd.thMM_spec h

theorem thMM_ne_zero (h : B.StdOK) : B.thMM ≠ 0 := B.toCd.thMM_ne_zero h

theorem thZero_ne_zero (h : B.StdOK) (N N' : ℕ) : B.thZero N N' ≠ 0 := B.toCd.thZero_ne_zero h N N'

theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h : TaylorLogMetric.admitted D N N' L L') :
    TaylorLogMetric.admitted D N N' L (StandardLatticesGL3.stdL D N') :=
  ⟨h.1, h.2.1, h.2.2.1, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N'⟩

theorem first_coordinate_admissible {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h : TaylorLogMetric.admitted D N N' L L') :
    TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') :=
  Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D N N' h.1 h.2.1

theorem thMoved_mem (hL : B.LatAll) {N N' : ℕ} (h0 : B.ThZeroMem N N') {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    B.thMoved N N' L L' ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L L') :=
  B.toCd.thMoved_mem hL h0 hA

theorem thMoved_ne_zero (hS : B.StdOK) (hL : B.LatAll) {N N' : ℕ} (h0 : B.ThZeroMem N N')
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') : B.thMoved N N' L L' ≠ 0 := by
  have hH := formV_herm (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'
  have a0 := hL.1 N N' _ _ (first_coordinate_admissible hA)
  have a1 := hL.1 N N' _ _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)
  have a2 := hL.1 N N' _ _ hA
  have c01 := hL.2 N N' _ _ _ _ (first_coordinate_admissible hA) (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)
  have c12 := hL.2 N N' _ _ _ _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA) hA
  have h1 := _root_.Formalism.L2.Th1.H.interTh _ _ hH _ _ _ a1.2 c01.1 _ h0
  have n1 := inter_ne_zero _ hH _ _ _ a0.1 a1.1 a0.2 a1.2 c01.1 c01.2 h0.2 (B.thZero_ne_zero hS N N')
  exact inter_ne_zero _ hH _ _ _ a1.1 a2.1 a1.2 a2.2 c12.1 c12.2 h1.2 n1

theorem eNat_mem_ne (hS : B.StdOK) (hL : B.LatAll) {N N' : ℕ} (h0 : B.ThZeroMem N N') (χ : TaylorLogMetric.IdE D → ℂ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') (hχ : chiFac χ N N' L L' ≠ 0) :
    B.eNat χ N N' L L' ∈ TaylorLogMetric.Th D B.tor L L' ∧ B.eNat χ N N' L L' ≠ 0 := by
  have e : B.eNat χ N N' L L' = chiFac χ N N' L L' • B.thMoved N N' L L' := rfl
  refine ⟨mem_ThSp_of D B.tor _ _ ?_, ?_⟩
  · rw [e]; exact Submodule.smul_mem _ _ (B.thMoved_mem hL h0 hA)
  · rw [e]; exact smul_ne_zero hχ (B.thMoved_ne_zero hS hL h0 hA)

theorem thZeroMem_of (hS : B.StdOK) (hA : B.AreaOK) {N N' : ℕ} (h0 : B.Lat0OK N N') (hq : B.QInt0 N N') :
    B.ThZeroMem N N' :=
  B.toCd.thZeroMem_of hS hA h0 hq

end Base

theorem area_eq (L : PeriodPair) : TaylorLogMetric.area L.lattice.toAddSubgroup = Formalism.L2.Th1.F.area L :=
  Cd.area_eq L

theorem Base.areaOK {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.AreaOK :=
  B.toCd.areaOK

theorem Base.omega_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.ω₀ ∈ B.L.lattice :=
  B.toCd.omega_mem

theorem Base.stdOK_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (half : B.ω₀ / 2 ∉ B.L.lattice)
    (isom : IsIsom (matH (blk4 (hOne B.L D.what₂.Tau))) (stdH B.L (Fin 4 × D.what₂.Tau))
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (betaStd : ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
      alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x = stdChar B.L B.ω₀ x)
    (betaSemi : IsSemiChar (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))))
    (selfDual : IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)))
    (idx₁ : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0)
    (idx₂ : relIdx (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0) : B.StdOK :=
  B.toCd.stdOK_of half isom betaStd betaSemi selfDual idx₁ idx₂

section Lat0

variable (D : D7) {N N' : ℕ}

theorem homL_std_entry {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.homL D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  Cd.homL_std_entry (Car.ofRec D) hA i j

theorem YYl_std_entry {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.YYl D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ D.host.AA0 :=
  Cd.YYl_std_entry (Car.ofRec D) hA i j

theorem single_mem_homL (i : Fin N') (j : Fin N) :
    (Matrix.single i j (1 : D.host.E)) ∈ TaylorLogMetric.homL D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') :=
  Cd.single_mem_homL (Car.ofRec D) i j

def putE (D : D7) (N N' : ℕ) (i : Fin N') (j : Fin N) : (D.what₂.Tau → ℂ) →+ TaylorLogMetric.VC D N N' where
  toFun v := fun τ i' j' => if i' = i ∧ j' = j then v τ else 0
  map_zero' := by funext τ i' j'; simp
  map_add' := by intro a b; funext τ i' j'; by_cases h : i' = i ∧ j' = j <;> simp [h]

theorem Lat0 (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat (lamMM D (TaylorLogMetric.lamOf D cc δ)) N N' :=
  Cd.Lat0 (Car.ofRec D) cc δ

end Lat0

theorem Base.lat0OK {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (N N' : ℕ) : B.Lat0OK N N' :=
  B.toCd.lat0OK N N'

theorem int_of_sign {r : ℝ} (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) = 1 ∨
    Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) = -1) : ∃ m : ℤ, r = (m : ℝ) :=
  Cd.int_of_sign h

section Gen

variable (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) {n : Type} [Fintype n] [DecidableEq n]
  (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))

theorem qInt_of_stdOK (h : StdOK L ω₀ c ΛM g) {v : n → ℂ} (hv : v ∈ ΛM) :
    ∃ m : ℤ, qOf c (matH (hOne L n)) v = (m : ℝ) :=
  Cd.qInt_of_stdOK L ω₀ c ΛM g h hv

end Gen

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem qInt0 (hS : B.StdOK) (N N' : ℕ) : B.QInt0 N N' := B.toCd.qInt0 hS N N'

theorem thZeroMem (hS : B.StdOK) (N N' : ℕ) : B.ThZeroMem N N' := B.toCd.thZeroMem hS N N'

theorem vec_parts (hS : B.StdOK) (hL : B.LatAll) (χ : TaylorLogMetric.IdE D → ℂ)
    (hχ : ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → chiFac χ N N' L L' ≠ 0) :
    ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' →
      B.eNat χ N N' L L' ∈ TaylorLogMetric.Th D B.tor L L' ∧ B.eNat χ N N' L L' ≠ 0 :=
  fun N N' _ _ hA => B.eNat_mem_ne hS hL (B.thZeroMem hS N N') χ hA (hχ N N' _ _ hA)

end Base

theorem inter_self {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (Λ : AddSubgroup V)
    (α : V → ℂ) (hα : IsSemiChar H Λ α) {F : V → ℂ} (hF : F ∈ fixedBy H α Λ) : inter H α Λ Λ F = F := by
  funext z
  have hS : IsReps Λ Λ ({0} : Finset V) :=
    ⟨fun x hx => by rw [Finset.mem_singleton.1 hx]; exact Λ.zero_mem,
      fun x hx y hy _ => by rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy],
      fun y hy => ⟨0, Finset.mem_singleton_self 0, by simpa using hy⟩⟩
  rw [InterReps_of semicharacterHom V H hH Λ Λ α hα F hF {0} hS z]
  have h1 : relIdx Λ Λ = 1 := AddSubgroup.relIndex_self Λ
  rw [h1]
  simp only [sumU, Finset.sum_singleton, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul]
  exact hF 0 Λ.zero_mem z

theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  apply le_antisymm
  · unfold TaylorLogMetric.detId
    rw [Submodule.span_le]
    rintro x ⟨A, hA, rfl⟩
    have hent : ∀ i j, A i j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
      intro i j
      have := (mem_stdL D _).1 (hA _ (single_mem_stdL D j)) i
      simpa using this
    choose A' hA' using hent
    have e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of A') := by
      ext i j; simp [hA']
    show A.det ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · rw [Submodule.one_le]
    exact Submodule.subset_span ⟨1, fun v hv => by simpa using hv, by simp⟩

theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  let _ := D.host.cmStar
  have h := hχ.2 (1 : unitary D.host.E)
  have e : Submodule.span (𝓞 D.host.E) {((1 : unitary D.host.E) : D.host.E)} = 1 := by
    rw [Submodule.one_eq_span]; rfl
  rw [e] at h
  rw [h]; simp

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem thHalf_mem (hS : B.StdOK) (hL : B.LatAll) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    B.thHalf N N' L ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) :=
  B.toCd.thHalf_mem hS hL hA

end Base

section Rec
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem exp_pi_int (b : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))
    = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))) :=
  Cd.exp_pi_int b

theorem al_sign (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T x = 1 ∨ TaylorLogMetric.al D T x = -1 :=
  Cd.al_sign (Car.ofRec D) ⟨T.emb, T.abelian₂⟩ x

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem latAll (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) : B.LatAll :=
  B.toCd.latAll hcc hδ h0

theorem chiFac_ne_zero (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') : chiFac χ N N' L L' ≠ 0 := by
  have h := character_unit_on_determinant D χ hχ
  have h1 := h N _ L hA.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hA.2.2.1
  have h2 := h N' _ L' hA.2.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N') hA.2.2.2
  refine mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)
  · intro e; rw [e] at h1; simp at h1
  · intro e; rw [e] at h2; simp at h2

theorem vec_mem_ne (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) :
    ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' →
      B.eNat χ N N' L L' ∈ TaylorLogMetric.Th D B.tor L L' ∧ B.eNat χ N N' L L' ≠ 0 :=
  B.vec_parts hS (B.latAll hcc hδ h0) χ fun _ _ _ _ hA => chiFac_ne_zero χ hχ hA

theorem chiFac_norm (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') : ‖chiFac χ N N' L L'‖ = 1 := by
  have h := character_unit_on_determinant D χ hχ
  have h1 := h N _ L hA.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hA.2.2.1
  have h2 := h N' _ L' hA.2.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N') hA.2.2.2
  unfold chiFac
  rw [norm_mul, norm_zpow, norm_zpow, h1, h2, one_zpow, one_zpow, mul_one]

theorem eNat_normSq (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    TaylorLogMetric.normSq D B.tor (TaylorLogMetric.La D B.tor L L') (B.eNat χ N N' L L')
      = TaylorLogMetric.normSq D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (B.thZero N N') := by
  have hL := B.latAll hcc hδ h0
  have hI := theta_operator_isometry D cc hcc δ hδ
  have e : B.eNat χ N N' L L' = fun z => chiFac χ N N' L L' * B.thMoved N N' L L' z := rfl
  rw [e, normSq_const_mul, chiFac_norm χ hχ hA, one_pow, one_mul]
  have m0 : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of D B.tor _ _ (B.thZeroMem hS N N')
  have m1 : B.thHalf N N' L ∈ TaylorLogMetric.Th D B.tor L (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of D B.tor _ _ (B.thHalf_mem hS hL hA)
  have s2 := hI N N' _ _ _ _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA) hA _ m1
  have s1 := hI N N' _ _ _ _ (first_coordinate_admissible hA) (isAdmissible_flagPair_of_unitriangular_left_automorphism hA) _ m0
  exact s2.trans s1

theorem th_indep (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) : ThetaNormIndependent D B.tor (B.eNat χ) :=
  fun _ _ _ _ _ _ h₁ h₂ => (B.eNat_normSq hcc hδ h0 hS χ hχ h₁).trans (B.eNat_normSq hcc hδ h0 hS χ hχ h₂).symm

theorem th_U (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) : th22U D B.tor (B.eNat χ) :=
  fun N N' L L' hA x => theta_unitary_linkage D cc hcc δ hδ N N' L L' hA _ (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1 x

end Base

end Rec

section Isom

variable {D : D7}

def emb4 (D : D7) (x : Fin 4 → D.host.E) : Fin 4 × D.what₂.Tau → ℂ := fun w => TaylorLogMetric.embT D w.2 (x w.1)

theorem span_range_emb4_eq_top (D : D7) : Submodule.span ℂ (Set.range (emb4 D)) = ⊤ :=
  Cd.span_range_emb4_eq_top (Car.ofRec D)

theorem isoK_hermitian_sum_eq_emb4_hermitian_sum (γ : IsoK D) (x y : Fin 4 → D.host.E) :
    ∑ w, D.host.φ₀ ((γ.g x w : D.host.K) : D.host.E) * conj (D.host.φ₀ ((γ.g y w : D.host.K) : D.host.E))
      = ∑ w, emb4 D x w * conj (emb4 D y w) :=
  Cd.isoK_hermitian_sum_eq_emb4_hermitian_sum (D := Car.ofRec D) γ x y

theorem blockFourfold_hOne_eq_hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] :
    blk4 (hOne L n) = hOne L (Fin 4 × n) :=
  Cd.blockFourfold_hOne_eq_hOne L n

theorem Base.isomOK {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) :
    IsIsom (matH (blk4 (hOne B.L D.what₂.Tau))) (stdH B.L (Fin 4 × D.what₂.Tau))
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :=
  B.toCd.isomOK

theorem Base.stdOK_of' {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (half : B.ω₀ / 2 ∉ B.L.lattice)
    (betaStd : ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
      alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x = stdChar B.L B.ω₀ x)
    (betaSemi : IsSemiChar (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))))
    (selfDual : IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)))
    (idx₁ : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0)
    (idx₂ : relIdx (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0) : B.StdOK :=
  B.toCd.stdOK_of' half betaStd betaSemi selfDual idx₁ idx₂

end Isom

section KapInh

variable {D : D7}

theorem exists_prime_over (D : D7) (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K), ((p : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := by
  have : Fact p.Prime := ⟨hp⟩
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP, hO⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (Ideal.span {(p : ℤ)}) (S := 𝓞 D.host.K)
  have hmem : ((p : ℕ) : 𝓞 D.host.K) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [← hO.over]; exact Ideal.mem_span_singleton_self _
    have h2 := Ideal.mem_comap.1 h1
    simpa using h2
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  exact ⟨⟨P, hP.isPrime, hne⟩, hmem⟩

theorem exists_gen (D : D7) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) :
    ∃ π : 𝓞 D.host.K, 𝔭.asIdeal ^ classNumber D.host.K = Ideal.span {π} := by
  have hmem : 𝔭.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 D.host.K)) := mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot
  have h1 : ClassGroup.mk0 (⟨𝔭.asIdeal, hmem⟩ ^ classNumber D.host.K : nonZeroDivisors (Ideal (𝓞 D.host.K))) = 1 := by
    rw [map_pow]; exact pow_card_eq_one
  have h2 := (ClassGroup.mk0_eq_one_iff (Submonoid.pow_mem _ hmem _)).1 (by simpa using h1)
  obtain ⟨π, hπ⟩ := h2.principal
  exact ⟨π, hπ⟩

end KapInh

end Formalism.L2.Ker
