module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

open MvPolynomial

namespace Bl.general_b_fact_right_alt

theorem goal1 {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {ι : Type*} [Fintype ι]
    {G : MvPolynomial ι K} {d : ℕ} (hG : IsHomogeneous G d) (c : S) (f : ι → S) :
    aeval (fun v => c * f v) G = c ^ d * aeval f G := by
  simpa only [aeval_def, eval₂_eq_eval_map, Pi.smul_def, smul_eq_mul] using
    (hG.map (algebraMap K S)).eval_smul c f

end Bl.general_b_fact_right_alt
