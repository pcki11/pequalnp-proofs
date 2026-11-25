import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_9400

open scoped BigOperators

abbrev F := ZMod 2
abbrev V := Fin 5 → F
abbrev Space := Submodule F V
noncomputable abbrev dim (A : Space) := Module.finrank F A

def pairing : V ≃ₗ[F] Module.Dual F V := dotProductEquiv F (Fin 5)

theorem pairing_comm (x y : V) : pairing x y = pairing y x := dotProduct_comm x y

theorem ambient_dim : Module.finrank F V = 5 := by
  simp [V]

def bits (i : Fin 32) : V := fun k => if i.val.testBit k.val then 1 else 0

def rows : List ℕ := [0, 2863311530, 3435973836, 1717986918, 4042322160,
  1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990,
  267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780,
  2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210,
  3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710]

theorem bits_bijective : Function.Bijective bits := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · show ∀ i j, bits i = bits j → i = j
    decide +kernel
  · simp [V, Fintype.card_pi, ZMod.card]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem matrix_spec : ∀ i j : Fin 32,
    (rows.getD i.val 0).testBit j.val = false ↔ pairing (bits i) (bits j) = 0 := by
  decide +kernel

noncomputable def points (A : Space) : Finset V := by
  classical
  exact Finset.univ.filter fun x => x ∈ A ∧ x ≠ 0

theorem mem_points {x : V} {A : Space} : x ∈ points A ↔ x ∈ A ∧ x ≠ 0 := by
  classical
  simp [points]

theorem card_points (A : Space) : (points A).card = 2 ^ dim A - 1 := by
  classical
  let carrier : Finset V := Finset.univ.filter (fun x => x ∈ A)
  have eq : points A = carrier.erase 0 := by
    ext x
    simp [mem_points, carrier, and_comm]
  have hz : 0 ∈ carrier := by simp [carrier]
  let : Fintype A := Fintype.ofFinite A
  have hc : carrier.card = Fintype.card A := by
    let e : (↥carrier) ≃ A :=
      Equiv.subtypeEquivRight fun x => by simp [carrier]
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  rw [eq, Finset.card_erase_of_mem hz, hc, Module.card_eq_pow_finrank (K := F), ZMod.card]

def hyper (y : V) : Space := LinearMap.ker (pairing y)

theorem hyper_dim {y : V} (hy : y ≠ 0) : dim (hyper y) = 4 := by
  have hn : pairing y ≠ 0 := fun e => hy (pairing.injective (e.trans (map_zero pairing).symm))
  have hr : (pairing y).range = ⊤ := LinearMap.range_eq_top.mpr (LinearMap.surjective_of_ne_zero hn)
  have hd := LinearMap.finrank_range_add_finrank_ker (pairing y)
  rw [hr, finrank_top, ambient_dim] at hd
  have hd' : 1 + dim (hyper y) = 5 := by simpa [hyper] using hd
  omega

theorem dim_le_ambient (A : Space) : dim A ≤ 5 :=
  (Submodule.finrank_le A).trans_eq ambient_dim

theorem lower_inf {A B H : Space} (hA : A ≤ H) (hB : B ≤ H) :
    dim A + dim B ≤ dim H + dim (A ⊓ B) := by
  have hr : dim (A ⊔ B) ≤ dim H := Submodule.finrank_mono (sup_le hA hB)
  have eq : dim (A ⊔ B) + dim (A ⊓ B) = dim A + dim B :=
    Submodule.finrank_sup_add_finrank_inf_eq A B
  omega

theorem inter_points (A B : Space) : points A ∩ points B = points (A ⊓ B) := by
  ext v
  simp only [Finset.mem_inter, mem_points, Submodule.mem_inf]
  tauto

theorem space_sum {A B : Space} (h : ∀ x ∈ A, ∀ y ∈ B, pairing x y = 0) :
    dim A + dim B ≤ 5 := by
  have le : A.map pairing.toLinearMap ≤ B.dualAnnihilator := by
    rintro f ⟨x, hx, rfl⟩
    exact (Submodule.mem_dualAnnihilator (W := B) (pairing x)).mpr (h x hx)
  have hle := Submodule.finrank_mono le
  rw [LinearEquiv.finrank_map_eq] at hle
  have eq := Subspace.finrank_add_finrank_dualAnnihilator_eq B
  rw [ambient_dim] at eq
  change dim B + Module.finrank F B.dualAnnihilator = 5 at eq
  change dim A ≤ Module.finrank F B.dualAnnihilator at hle
  omega

def weight : ℕ → ℕ
  | 0 => 0
  | 1 => 5
  | 2 => 12
  | 3 => 20
  | _ => 60

theorem rectangle_charge : ∀ a b : Fin 6, a.val + b.val ≤ 5 →
    weight a.val * (2 ^ b.val - 1) + weight b.val * (2 ^ a.val - 1) ≤ 144 := by
  decide +kernel

theorem points_mono {A B : Space} (hAB : A ≤ B) : points A ⊆ points B := by
  intro x hx
  obtain ⟨hxA, hx0⟩ := mem_points.mp hx
  exact mem_points.mpr ⟨hAB hxA, hx0⟩

theorem few_outside {A B H : Space} (hA : A ≤ H) (hB : B ≤ H) (hH : dim H = 4)
    (a : dim A = 2) (b : dim B = 3) : (points A \ points B).card ≤ 2 := by
  classical
  have rank := lower_inf hA hB
  have d : 1 ≤ dim (A ⊓ B) := by omega
  have c : (2 : ℕ) ^ 1 ≤ 2 ^ dim (A ⊓ B) := Nat.pow_le_pow_right (by decide) d
  rw [Finset.card_sdiff, inter_points, card_points, card_points, a]
  rw [inf_comm B A]
  change 3 - ((2 : ℕ) ^ dim (A ⊓ B) - 1) ≤ 2
  omega

theorem two_large {A B H : Space} (hA : A ≤ H) (hB : B ≤ H) (hH : dim H = 4)
    (a : dim A = 3) (b : dim B = 3) : (points A ∪ points B).card ≤ 11 := by
  classical
  have rank := lower_inf hA hB
  have d : 2 ≤ dim (A ⊓ B) := by omega
  have c : (2 : ℕ) ^ 2 ≤ 2 ^ dim (A ⊓ B) := Nat.pow_le_pow_right (by decide) d
  rw [Finset.card_union, inter_points, card_points, card_points, card_points, a, b]
  norm_num at c ⊢
  omega

theorem cover_hyperplane {ι : Type*} (T : Finset ι) (A : ι → Space) (H : Space)
    (hH : dim H = 4) (inside : ∀ i ∈ T, A i ≤ H)
    (cover : ∀ x ∈ points H, ∃ i ∈ T, x ∈ points (A i)) :
    60 ≤ ∑ i ∈ T, weight (dim (A i)) := by
  classical
  have d (i) (hi : i ∈ T) : dim (A i) ≤ 4 :=
    (Submodule.finrank_mono (inside i hi)).trans_eq hH
  by_cases top : ∃ i ∈ T, dim (A i) = 4
  · obtain ⟨i, hi, di⟩ := top
    have le := Finset.single_le_sum (f := fun j => weight (dim (A j))) (fun _ _ => Nat.zero_le _) hi
    simpa [di, weight] using le
  push Not at top
  let G := T.filter fun i => dim (A i) = 3
  have Gsub : G ⊆ T := Finset.filter_subset _ _
  by_cases many : 3 ≤ G.card
  · have le := Finset.sum_le_sum_of_subset_of_nonneg Gsub (fun _ _ _ => Nat.zero_le _)
      (f := fun i => weight (dim (A i)))
    have eq : (∑ i ∈ G, weight (dim (A i))) = G.card * 20 := by
      calc
        _ = ∑ _i ∈ G, 20 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [(Finset.mem_filter.mp hi).2, weight]
        _ = _ := by simp
    omega
  push Not at many
  have cardH : (points H).card = 15 := by rw [card_points, hH]; decide
  by_cases empty : G.card = 0
  · have need : 15 ≤ ∑ i ∈ T, (points (A i)).card := by
      rw [← cardH]
      refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
      intro x hx
      exact Finset.mem_biUnion.mpr (cover x hx)
    have charge : ∑ i ∈ T, (4 * (points (A i)).card) ≤ ∑ i ∈ T, weight (dim (A i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have d' := d i hi
      have not4 := top i hi
      have not3 : dim (A i) ≠ 3 := by
        intro di
        have hm : i ∈ G := Finset.mem_filter.mpr ⟨hi, di⟩
        exact (Finset.card_pos.mpr ⟨i, hm⟩).ne' empty
      rw [card_points]
      have ds : dim (A i) ≤ 2 := by omega
      interval_cases hdim : dim (A i) <;> first | omega | decide
    rw [← Finset.mul_sum] at charge
    omega
  let occupied := G.biUnion fun i => points (A i)
  have occupied_sub : occupied ⊆ points H := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact points_mono (inside i (Gsub hi)) hxi
  have occupied_bound :
      (G.card = 1 ∧ occupied.card ≤ 7) ∨ (G.card = 2 ∧ occupied.card ≤ 11) := by
    have casesG : G.card = 1 ∨ G.card = 2 := by omega
    rcases casesG with one | two
    · left
      obtain ⟨i, eq⟩ := Finset.card_eq_one.mp one
      have hi : i ∈ G := by simp [eq]
      have di := (Finset.mem_filter.mp hi).2
      refine ⟨one, ?_⟩
      simp [occupied, eq, card_points, di]
    · right
      obtain ⟨i, j, _, eq⟩ := Finset.card_eq_two.mp two
      have hi : i ∈ G := by simp [eq]
      have hj : j ∈ G := by simp [eq]
      refine ⟨two, ?_⟩
      simpa [occupied, eq] using two_large (inside i (Gsub hi)) (inside j (Gsub hj)) hH
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have remain : (points H \ occupied).card ≤ ∑ i ∈ T, (points (A i) \ occupied).card := by
    refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
    intro x hx
    obtain ⟨hxH, hxout⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨i, hi, hxi⟩ := cover x hxH
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨hxi, hxout⟩⟩
  rw [Finset.card_sdiff_of_subset occupied_sub, cardH] at remain
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < G.card by omega)
  have jsub : points (A j) ⊆ occupied := fun x hx => Finset.mem_biUnion.mpr ⟨j, hj, hx⟩
  have charge : ∑ i ∈ T, ((if dim (A i) = 3 then 20 else 0) +
      5 * (points (A i) \ occupied).card) ≤ ∑ i ∈ T, weight (dim (A i)) := by
    apply Finset.sum_le_sum
    intro i hi
    have d' := d i hi
    have not4 := top i hi
    by_cases big : dim (A i) = 3
    · have iG : i ∈ G := Finset.mem_filter.mpr ⟨hi, big⟩
      have sub : points (A i) ⊆ occupied := fun x hx => Finset.mem_biUnion.mpr ⟨i, iG, hx⟩
      simp [big, weight, Finset.sdiff_eq_empty_iff_subset.mpr sub]
    · have small : (points (A i) \ occupied).card ≤ (points (A i)).card :=
        Finset.card_le_card Finset.sdiff_subset
      have two : dim (A i) = 2 → (points (A i) \ occupied).card ≤ 2 := by
        intro di
        refine (Finset.card_le_card ?_).trans
          (few_outside (inside i hi) (inside j (Gsub hj)) hH di (Finset.mem_filter.mp hj).2)
        intro x hx
        obtain ⟨hxi, hout⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hxi, fun hxj => hout (jsub hxj)⟩
      simp only [big, ite_false, zero_add]
      have ds : dim (A i) ≤ 2 := by omega
      interval_cases hdim : dim (A i)
      · simp [weight, card_points, hdim] at small ⊢
        omega
      · simp [weight, card_points, hdim] at small ⊢
        omega
      · simp [weight]
        have htwo := two rfl
        omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite] at charge
  simp only [Finset.sum_const, nsmul_eq_mul] at charge
  change G.card * 20 + 5 * (∑ i ∈ T, (points (A i) \ occupied).card) ≤ _ at charge
  rcases occupied_bound with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem side_total {ι : Type*} [Fintype ι] (A B : ι → Space)
    (orth : ∀ k x y, x ∈ A k → y ∈ B k → pairing x y = 0)
    (cover : ∀ x y, pairing x y = 0 → ∃ k, x ∈ A k ∧ y ∈ B k) :
    1860 ≤ ∑ k, weight (dim (A k)) * (points (B k)).card := by
  classical
  let all := points (⊤ : Space)
  have card_all : all.card = 31 := by
    change (points (⊤ : Space)).card = 31
    rw [card_points, show dim (⊤ : Space) = 5 by rw [dim, finrank_top, ambient_dim]]
    decide +kernel
  have for_y (y : V) (hy : y ∈ all) :
      60 ≤ ∑ k, if y ∈ B k then weight (dim (A k)) else 0 := by
    have hy0 := (mem_points.mp hy).2
    rw [← Finset.sum_filter]
    let T : Finset ι := Finset.univ.filter fun k => y ∈ B k
    apply cover_hyperplane T A (hyper y) (hyper_dim hy0)
    · intro k hk x hx
      have yz := orth k x y hx (Finset.mem_filter.mp hk).2
      exact LinearMap.mem_ker.mpr ((pairing_comm y x).trans yz)
    · intro x hx
      obtain ⟨hxy, hx0⟩ := mem_points.mp hx
      have hz := (pairing_comm x y).trans (LinearMap.mem_ker.mp hxy)
      obtain ⟨k, hA, hB⟩ := cover x y hz
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩, mem_points.mpr ⟨hA, hx0⟩⟩
  calc
    1860 = ∑ _y ∈ all, 60 := by simp [card_all]
    _ ≤ ∑ y ∈ all, ∑ k, if y ∈ B k then weight (dim (A k)) else 0 :=
      Finset.sum_le_sum for_y
    _ = ∑ k, ∑ y ∈ all, if y ∈ B k then weight (dim (A k)) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have filter_eq : (all.filter fun y => y ∈ B k) = points (B k) := by
        ext y
        simp only [all, Finset.mem_filter, mem_points, Submodule.mem_top, true_and]
        exact and_comm
      rw [← Finset.sum_filter, filter_eq]
      simp [Nat.mul_comm]

theorem count_rectangles {ι : Type*} [Fintype ι] (A B : ι → Space)
    (orth : ∀ k x y, x ∈ A k → y ∈ B k → pairing x y = 0)
    (cover : ∀ x y, pairing x y = 0 → ∃ k, x ∈ A k ∧ y ∈ B k) :
    3720 ≤ Fintype.card ι * 144 := by
  classical
  have s1 := side_total A B orth cover
  have s2 := side_total B A
    (fun k x y hx hy => (pairing_comm x y).trans (orth k y x hy hx))
    (fun x y h => by
      obtain ⟨k, hy, hx⟩ := cover y x ((pairing_comm y x).trans h)
      exact ⟨k, hx, hy⟩)
  calc
    3720 ≤ (∑ k, weight (dim (A k)) * (points (B k)).card) +
        (∑ k, weight (dim (B k)) * (points (A k)).card) := by omega
    _ = ∑ k, (weight (dim (A k)) * (points (B k)).card +
              weight (dim (B k)) * (points (A k)).card) := by rw [Finset.sum_add_distrib]
    _ ≤ ∑ _k : ι, 144 := by
      apply Finset.sum_le_sum
      intro k _
      have ad := dim_le_ambient (A k)
      have bd := dim_le_ambient (B k)
      let a : Fin 6 := ⟨dim (A k), by omega⟩
      let b : Fin 6 := ⟨dim (B k), by omega⟩
      rw [card_points, card_points]
      exact rectangle_charge a b (space_sum fun x hx y hy => orth k x y hx hy)
    _ = _ := by simp

def spanBits (s : Finset (Fin 32)) : Space := Submodule.span F (bits '' (s : Set (Fin 32)))

theorem in_spanBits {s : Finset (Fin 32)} {i : Fin 32} (hi : i ∈ s) :
    bits i ∈ spanBits s :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem spanBits_orth {s t : Finset (Fin 32)}
    (h : ∀ i ∈ s, ∀ j ∈ t, pairing (bits i) (bits j) = 0) :
    ∀ x ∈ spanBits s, ∀ y ∈ spanBits t, pairing x y = 0 := by
  have first (j : Fin 32) (hj : j ∈ t) : spanBits s ≤ hyper (bits j) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact LinearMap.mem_ker.mpr ((pairing_comm _ _).trans (h i hi j hj))
  intro x hx y hy
  have hsecond : spanBits t ≤ hyper x := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact LinearMap.mem_ker.mpr ((pairing_comm _ _).trans (LinearMap.mem_ker.mp (first j hj hx)))
  exact LinearMap.mem_ker.mp (hsecond hy)

theorem no_small_cover :
    ¬ (∃ L : List (Finset (Fin 32) × Finset (Fin 32)), L.length ≤ 25 ∧
      (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (rows.getD i.val 0).testBit j.val = false) ∧
      ∀ i j : Fin 32, (rows.getD i.val 0).testBit j.val = false →
        ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, short, soundness, completeness⟩
  let A (k : Fin L.length) := spanBits L[k.val].1
  let B (k : Fin L.length) := spanBits L[k.val].2
  have orth : ∀ k x y, x ∈ A k → y ∈ B k → pairing x y = 0 := by
    intro k x y hx hy
    exact spanBits_orth
      (fun i hi j hj => (matrix_spec i j).mp
        (soundness L[k.val] (List.getElem_mem _) i hi j hj)) x hx y hy
  have cover : ∀ x y, pairing x y = 0 → ∃ k, x ∈ A k ∧ y ∈ B k := by
    intro x y h
    obtain ⟨i, rfl⟩ := bits_bijective.surjective x
    obtain ⟨j, rfl⟩ := bits_bijective.surjective y
    obtain ⟨r, hr, hi, hj⟩ := completeness i j ((matrix_spec i j).mpr h)
    obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hr
    subst r
    exact ⟨⟨k, hk⟩, in_spanBits hi, in_spanBits hj⟩
  have bound := count_rectangles A B orth cover
  rw [Fintype.card_fin] at bound
  omega

end PEqualNP.Outside.L_meta_9400

theorem PEqualNP.Outside.L_meta_9400 : ¬ (∃ L : List (Finset (Fin 32) × Finset (Fin 32)), L.length ≤ 25 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 32) (j : Fin 32), (([0, 2863311530, 3435973836, 1717986918, 4042322160, 1515870810, 1010580540, 2526451350, 4278255360, 1437226410, 869020620, 2573637990, 267390960, 2774181210, 3275539260, 1771465110, 4294901760, 1431677610, 859032780, 2576967270, 252702960, 2779077210, 3284352060, 1768527510, 16776960, 2857719210, 3425907660, 1721342310, 4027518960, 1520805210, 1019462460, 2523490710] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) :=
  PEqualNP.Outside.L_meta_9400.no_small_cover
