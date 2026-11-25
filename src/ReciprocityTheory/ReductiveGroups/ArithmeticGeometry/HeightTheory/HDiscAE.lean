module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem comp_facts (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
    letI := algOpKT (K := K) d.D d.N la
    IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) ∧
      IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      IsDedekindDomain (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) ∧
      IsFractionRing (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) (OmS (Ω c) d.D d.N) := by
  classical
  letI iKS : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iOS : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  letI iOK : Algebra (Op d.D d.N la) (KTf K d.D d.N) := algOpKT (K := K) d.D d.N la
  haveI hF : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := NPA.op_isFractionRing d.D d.N la
  haveI hT : IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  haveI hFD : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    obtain ⟨_, _, hsp⟩ := hd.a4.choose_spec
    refine Module.finite_def.mpr ⟨Finset.univ.image (fun k => d.bvecG hd.sel hd.a4.choose k c),
      eq_top_iff.mpr fun y _ => ?_⟩
    obtain ⟨q, hq, p, hp⟩ := hsp (Pi.single c y)
    have hy := hp c
    rw [Pi.single_eq_same] at hy
    have hq' := hq c
    have hS : ∀ r : KTp K d.D d.N,
        d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) r) = d.sH c r := by
      intro r
      unfold Data.KTtoS
      exact IsFractionRing.lift_algebraMap _ _
    have hyy : y = ∑ k, (algebraMap _ (KTf K d.D d.N) (p k) / algebraMap _ (KTf K d.D d.N) q) •
        d.bvecG hd.sel hd.a4.choose k c := by
      show y = ∑ k, d.KTtoS h c (algebraMap _ (KTf K d.D d.N) (p k) /
        algebraMap _ (KTf K d.D d.N) q) * d.bvecG hd.sel hd.a4.choose k c
      simp only [map_div₀, hS]
      calc y = (d.sH c q)⁻¹ * (d.sH c q * y) := by
            rw [← mul_assoc, inv_mul_cancel₀ hq', one_mul]
        _ = (d.sH c q)⁻¹ * ∑ k, d.sH c (p k) * d.bvecG hd.sel hd.a4.choose k c :=
            congrArg (fun t => (d.sH c q)⁻¹ * t) hy
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
    rw [hyy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  haveI hsep : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := inferInstance
  haveI : IsDiscreteValuationRing (Op d.D d.N la) := Op_isDVR d.D d.N la
  refine ⟨hF, hT, hFD, hsep, ?_, ?_⟩
  · first
      | exact integralClosure.isDedekindDomain (A := Op d.D d.N la) (K := KTf K d.D d.N)
          (L := OmS (Ω c) d.D d.N)
  · first
      | exact integralClosure.isFractionRing_of_finite_extension (A := Op d.D d.N la)
          (K := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N)

theorem plOver_eq (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι) :
    letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
    d.PlOver la c = ValPl.PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N) := by
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  letI : Algebra (OT K d.D d.N) (OmS (Ω c) d.D d.N) := (d.OTtoS c).toAlgebra
  haveI : IsScalarTower (OT K d.D d.N) (Op d.D d.N la) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq fun x => (d.opToS_alg h la c x).symm
  ext w
  simp only [ValPl.PlacesOver, Data.PlOver, Set.mem_setOf_eq]
  rw [← ValPl.placesOver_iff_loc (R := OT K d.D d.N) (laT d.D d.N la) w]
  rfl

theorem comp_g (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι)
    (n : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ) :
    letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
    ∃ g : OmS (Ω c) d.D d.N, g ≠ 0 ∧ (∀ w ∈ d.PlOver la c, w g = n w) ∧
      ∀ y, (∀ w ∈ d.PlOver la c, 0 ≤ w y + (n w : WithTop ℤ)) ↔
        g * y ∈ integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := d.comp_facts hd h la c
  haveI := Op_isDVR (K := K) d.D d.N la
  obtain ⟨g, hg0, hg⟩ := HDiscVal.exists_val_eq (O := Op d.D d.N la) (F := KTf K d.D d.N) n
  rw [d.plOver_eq h la c]
  refine ⟨g, hg0, hg, fun y => ?_⟩
  rw [HDiscVal.mem_integralClosure_iff (Op d.D d.N la) (KTf K d.D d.N)]
  refine forall₂_congr fun w hw => ?_
  rw [AddValuation.map_mul, hg w hw, add_comm]

theorem comp_norm (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι)
    {g : OmS (Ω c) d.D d.N} (hg0 : g ≠ 0) (n : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ)
    (hg : ∀ w ∈ d.PlOver la c, w g = n w) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∃ u : Op d.D d.N la, IsUnit u ∧ Algebra.norm (KTf K d.D d.N) g =
      OpToKT d.D d.N la (unifOp d.D d.N la) ^
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
          (d.fze h c w : ℤ) * n w) * OpToKT d.D d.N la u := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := d.comp_facts hd h la c
  haveI := Op_isDVR (K := K) d.D d.N la
  obtain ⟨u, hu, hN⟩ := ValPl.norm_eq_places (O := Op d.D d.N la) (F := KTf K d.D d.N) g hg0
    (unifOp_irreducible d.D d.N la)
  refine ⟨u, hu, ?_⟩
  rw [hN]
  have hg' : ∀ w ∈ ValPl.PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N), w g = n w := by
    rw [← d.plOver_eq h la c]
    exact hg
  rw [d.plOver_eq h la c]
  congr 2
  refine finsum_congr fun w => finsum_congr fun hw => ?_
  rw [hg' w hw, WithTop.untopD_coe]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
