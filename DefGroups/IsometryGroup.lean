import Mathlib
import DefGroups.MyGroups

--Definition of an arbitrary Metric Space
class MyMetricSpace (α : Type*) where
  d : α → α → ℝ
  pos_def : ∀ x y : α, (d x y) = 0 ↔ x = y
  symm : ∀ x y : α, (d x y) = (d y x)
  triangle : ∀ x y z : α, (d x z) ≤ (d x y) + (d y z)

namespace MyMetricSpace

theorem d_nonneg {α : Type*} [MyMetricSpace α] : ∀ x y : α, 0 ≤ (d x y) := by
  intro x y
  rename_i inst
  have h1 : d x x = 0 := by
    simp [inst.pos_def]
  suffices h : d x x ≤ 2 * (d x y)
  rw [h1] at h
  simp at h
  exact h
  have h2 : d x x ≤ d x y + d y x := by
    exact inst.triangle x y x
  simp [inst.symm] at h2
  ring_nf at h2
  ring_nf
  exact h2


theorem eq_imp_d_zero {α : Type*} [MyMetricSpace α] (x y : α) (h : x = y) : d x y = 0 := by
  simp [pos_def]
  exact h

end MyMetricSpace


/-Defining an Isomorphic Isometry over a given metric space-/
@[ext]
structure MyIsometry {α : Type*} (inst : MyMetricSpace α) where
  func : α → α
  d_preserve : ∀ x y : α, inst.d x y = inst.d (func x) (func y)
  func_sur : ∀ y : α, ∃ x : α, func x = y

namespace MyIsometry

/-To define compostion of isometries (say f g), we need to
  1 ) take the functions to the composed function (f ∘ g)
  2 ) take the d_preserving hypotheses (of f and g) and create one for (f ∘ g)
  3 ) take the func_surjective hypotheses (of f and g) and create one for (f ∘ g)
-/

/-This theorem accomplishes step 2, given two isometries, it returns that the
composition preserves distance-/
theorem comp_eq_d_preserve {α : Type*} [M : MyMetricSpace α] (f g : α → α) (hdf : ∀ x y : α, M.d x y = M.d (f x) (f y)) (hdg : ∀ x y : α, M.d x y = M.d (g x) (g y)) :
  ∀ x y : α, M.d x y = M.d ((f ∘ g) x) ((f ∘ g) y) := by
  intro x y
  simp [Function.comp]
  calc M.d x y
    _ = M.d (g x) (g y) := by apply hdg
    _ = M.d (f (g x)) (f (g y)) := by apply hdf


/-This theorem accomplishes step 3, given two isometries, it returns that the
composition is surjective-/
theorem comp_eq_surj {α : Type*} [MyMetricSpace α] (f g : α → α) (hsf : ∀ y : α, ∃ x : α, f x = y) (hsg : ∀ y : α, ∃ x : α, g x = y) :
  ∀ y : α, ∃ x : α, (f ∘ g) x = y := by
  intro y
  simp [Function.comp]
  cases hsf y
  rename_i z h1
  cases hsg z
  rename_i x h2
  exists x
  rw [h2, h1]

/-Combines all three steps to make a composed isometry-/
def comp {α : Type*} [M : MyMetricSpace α] : MyIsometry M → MyIsometry M → MyIsometry M
  | mk f hdf hsf, mk g hdg hsg => mk (f ∘ g) (comp_eq_d_preserve f g hdf hdg) (comp_eq_surj f g hsf hsg)

/-Theorem that an Isometric Isomorphism is injective-/
theorem func_inj {α : Type*} [M : MyMetricSpace α] (f : MyIsometry M) (x y : α) (h : f.func x = f.func y) : x = y := by
  apply M.eq_imp_d_zero at h
  rw [←f.d_preserve] at h
  rw [M.pos_def] at h
  exact h

/-Defines Identity function for a metric space and proves it is an isometric isomorphism-/
def Id {α : Type*} [M : MyMetricSpace α] : MyIsometry M where
  func := fun x => x
  d_preserve := by
    simp
  func_sur := by
    intro y
    exists y


end MyIsometry

/-We Will Show
  1) Integers form a metric space
  2) The Isometries over it from a group under composition
-/

/-The metric for Integers will be the usual metric := |x - y|
Int.natAbs takes integers x y and returns |x - y| : ℕ
nat_to_real casts naturals to reals
-/

def nat_to_real : ℕ → ℝ
  | 0 => 0
  | Nat.succ n => (nat_to_real n) + 1

theorem zero_eq_zero : nat_to_real 0 = 0 := by rfl

theorem nat_to_real_monotone0 (n : ℕ) (h : 0 ≤ n) : 0 ≤ nat_to_real n := by
  induction n with
  |zero =>
    rfl
  |succ d hd =>
    simp at hd
    have h1 : nat_to_real d ≤ (nat_to_real d) + 1 := by
      simp
    have h2 : 0 ≤ (nat_to_real d) + 1 := by
      apply Real.orderedRing.le_trans 0 (nat_to_real d) ((nat_to_real d) + 1)
      exact hd
      exact h1
    rw [nat_to_real]
    exact h2

theorem nat_to_real_inj0 (n : ℕ) (h : nat_to_real n = 0) : n = 0 := by
  cases n
  rfl
  rename_i n
  have h1 : 0 ≤ n := by simp
  have h2 : 0 ≤ nat_to_real n := by exact nat_to_real_monotone0 n h1
  simp [nat_to_real] at h
  have h3 : nat_to_real n < nat_to_real n + 1 := by simp
  have h4 : 0 < nat_to_real n + 1 := by
    apply lt_of_le_of_lt h2 h3
  have h5 : nat_to_real n + 1 ≤ 0 := by
    simp [h]
  have h6 : nat_to_real n + 1 < nat_to_real n + 1 := by
    apply lt_of_le_of_lt h5 h4
  simp at h6


theorem nat_to_real_lin : ∀ a b : ℕ, nat_to_real (a + b) = nat_to_real a + nat_to_real b := by
  intro a b
  induction b with
  |zero =>
    simp
    rfl
  |succ d hd =>
    simp only [Nat.add_succ]
    simp [nat_to_real]
    rw [hd]
    ring

theorem nat_to_real_monotone : ∀ a b : ℕ, a ≤ b → nat_to_real a ≤ nat_to_real b := by
  intro a b h
  have h1 : 0 ≤ b - a := by simp [h]
  have h2 : 0 ≤ nat_to_real (b - a) := by exact nat_to_real_monotone0 (b - a) h1
  have h3 : nat_to_real a ≤ nat_to_real (b - a) + nat_to_real a := by simp [h2]
  rw [←nat_to_real_lin (b - a) a] at h3
  simp [Nat.add_comm] at h3
  simp [Nat.add_sub_cancel' h] at h3
  exact h3

theorem nat_to_real_inj : ∀ m n : Nat, nat_to_real m = nat_to_real n → m = n := by
  intro m n h
  induction n generalizing m with
  |zero =>
    simp at h
    simp [nat_to_real] at h
    apply nat_to_real_inj0 at h
    simp
    exact h
  |succ d hd =>
    cases m
    simp at h
    rw [nat_to_real] at h
    symm at h
    apply nat_to_real_inj0 at h
    simp at h

    rename_i m
    simp [nat_to_real] at h
    apply hd at h
    simp
    exact h

/-Proves that Int.natAbs obeys the triangle inequality-/
theorem natAbs_triangle  : ∀ a b c : ℤ, Int.natAbs (a - c) ≤ Int.natAbs (a - b) + Int.natAbs (b - c) := by
  intro a b c
  have h : a - c = (a - b) + (b - c) := by simp
  rw [h]
  apply Int.natAbs_add_le


instance MetricZ : MyMetricSpace Int where
  d := fun a b => nat_to_real (Int.natAbs (a - b))
  pos_def := by
    intro x y
    simp
    apply Iff.intro
    intro h
    apply nat_to_real_inj0 at h
    simp [Int.natAbs_eq_zero] at h
    calc x
      _ = x + 0 := by rw [Int.add_zero]
      _ = x + (-y + y) := by simp
      _ = (x - y) + y := by simp
      _ = 0 + y := by rw [h]
      _ = y := by simp

    intro h
    have h1 : x - y = 0 := by
      rw [h]
      exact Int.sub_self y
    rw [h1]
    simp [Int.natAbs]
    simp [nat_to_real]

  symm := by
    intro x y
    simp
    have h : Int.natAbs (x - y) = Int.natAbs (y - x) := by
      have h1 : y - x = -(x - y) := by simp
      rw [h1]
      simp only [Int.natAbs_neg]
    rw [h]

  triangle := by
    intro x y z
    simp
    let h := natAbs_triangle x y z
    let h1 := nat_to_real_monotone (Int.natAbs (x - z)) (Int.natAbs (x - y) + Int.natAbs (y - z)) h
    rw [nat_to_real_lin] at h1
    exact h1

def IsometriesOverZ := MyIsometry MetricZ


namespace IsometriesOverZ

/-Again to define the inverse of an isometry we need to construct 3 things
  1 ) The inverse function ℤ → ℤ
  2 ) The statement that it is d_preserving
  3 ) The statement that it is surjective
-/

/-This takes an isometric function to its "inverse"
We prove later that this is indeed the inverse-/
def inv_func : (Int → Int) → (Int → Int)
  | f => fun x => ((f 1) - (f 0)) * (x - f 0)

/-Proves that the "inv" of an isometry preserves distance-/
theorem inv_func_d_preserve (f : IsometriesOverZ) :
  ∀ x y : ℤ, MetricZ.d x y = MetricZ.d (inv_func f.func x) (inv_func f.func y) := by
  intro x y
  simp [inv_func]
  simp [MetricZ]
  simp [mul_sub]
  rw [←mul_sub]
  simp [Int.natAbs_mul]
  have h1 : nat_to_real 1 = 1 := by
    rw [Nat.one_eq_succ_zero]
    simp [nat_to_real]
  have h2 : MetricZ.d 1 0 = 1 := by
    simp [MetricZ]
    exact h1
  have h3 : MetricZ.d (f.func 1) (f.func 0) = 1 := by
    rw [←h2]
    exact Eq.symm (f.d_preserve 1 0)
  simp [MetricZ] at h3
  rw [←h1] at h3
  apply nat_to_real_inj at h3
  simp [h3]


/-To prove that the inverse we have defined is indeed the inverse, we first prove
that any Isometry over the integers is of the form "f(x) = f(0) + (f(1) - f(0)) * x"
After this result, the inverse and therefore the surjective hypothesis for the inverse
follow trivially
-/

/-We prove the general form in 3 steps
  Given an isometry f,
    1) ∀ d, f(d + 1) - f(d) = f(d) - f(d - 1)
    2) ∀ d, f(d + 1) - f(d) = f(1) - f(0)
    3) ∀ d, f(d) = f(0) + (f(1) - f(0)) * d
-/

/-This proves step 1-/
theorem consecutive_dif_same (f : IsometriesOverZ) (d : ℤ) : f.func (d + 1) - f.func d = f.func d - f.func (d - 1) := by
  have h : Int.natAbs (f.func (d + 1) - f.func (d - 1)) = 2 := by
    let h1 := f.d_preserve (d + 1) (d - 1)
    simp [MyMetricSpace.d] at h1
    apply nat_to_real_inj at h1
    symm at h1
    exact h1
  simp [Int.natAbs_eq_iff] at h

  have h7 : Int.natAbs (f.func d - f.func (d - 1)) = 1 := by
    let h1 := f.d_preserve d (d - 1)
    simp [MyMetricSpace.d] at h1
    apply nat_to_real_inj at h1
    symm at h1
    exact h1
  simp [Int.natAbs_eq_iff] at h7

  if h2 : f.func d - f.func (d - 1) = 1 then
    have h3 : f.func (d + 1) - f.func d = 1 := by
      if h4 : f.func (d + 1) - f.func (d - 1) = 2 then
        calc
          _ = f.func (d + 1) - f.func (d - 1) + f.func (d - 1) - f.func d := by ring
          _ = 2 - (f.func d - f.func (d - 1)) := by rw [h4]; ring
          _ = 2 - 1 := by rw [h2]
          _ = 1 := by rfl
      else
        simp [h4] at h
        have h5 : f.func (d + 1) - f.func d = -3 := by
          calc
            _ = f.func (d + 1) - f.func (d - 1) + f.func (d - 1) - f.func d := by simp
            _ = -2 - (f.func d - f.func (d - 1)) := by rw [h]; ring
            _ = -2 - 1 := by rw [h2]
            _ = -3 := by rfl
        have h : Int.natAbs (f.func (d + 1) - f.func d) = 1 := by
          let h1 := f.d_preserve (d + 1) d
          simp [MyMetricSpace.d] at h1
          apply nat_to_real_inj at h1
          symm at h1
          exact h1
        simp [Int.natAbs_eq_iff] at h
        simp [h5] at h
    rw [h2, h3]
  else
    simp [h2] at h7
    have h3 : f.func (d + 1) - f.func d = -1 := by
      if h4 : f.func (d + 1) - f.func (d - 1) = -2 then
        calc
          _ = f.func (d + 1) - f.func (d - 1) + f.func (d - 1) - f.func d := by ring
          _ = -2 - (f.func d - f.func (d - 1)) := by rw [h4]; ring
          _ = -2 + 1 := by rw [h7]; ring
          _ = -1 := by rfl
      else
        simp [h4] at h
        have h5 : f.func (d + 1) - f.func d = 3 := by
          calc
            _ = f.func (d + 1) - f.func (d - 1) + f.func (d - 1) - f.func d := by simp
            _ = 2 - (f.func d - f.func (d - 1)) := by rw [h]; ring
            _ = 2 + 1 := by rw [h7]; ring
            _ = 3 := by rfl
        have h : Int.natAbs (f.func (d + 1) - f.func d) = 1 := by
          let h1 := f.d_preserve (d + 1) d
          simp [MyMetricSpace.d] at h1
          apply nat_to_real_inj at h1
          symm at h1
          exact h1
        simp [Int.natAbs_eq_iff] at h
        simp [h5] at h
    rw [h3, h7]

/-This proves step 2-/
theorem consecutive_d_same (f : IsometriesOverZ) : ∀ n : Int, f.func (↑n + 1) - f.func (↑n) = (f.func 1 - f.func 0) := by
  intro n
  cases n
  rename_i n
  induction n with
  |zero =>
    rfl
  |succ d hd =>
    simp
    let h := consecutive_dif_same f (↑d + 1)
    simp at h
    simp at hd
    rw [h, hd]
  rename_i n
  induction n with
  |zero =>
    simp
    let h := consecutive_dif_same f 0
    simp at h;  symm
    exact h
  |succ d hd =>
    simp at hd
    let h := consecutive_dif_same f (Int.negSucc d)
    simp at h
    rw [h] at hd
    have h1 : (Int.negSucc (Nat.succ d) + 1) = Int.negSucc (d) := by rfl
    have h2 : (Int.negSucc (Nat.succ d)) = Int.negSucc (d + 1) := by rfl
    rw [h1, h2, hd]

/-This proves step 3-/
theorem generalFormIsometry (f : IsometriesOverZ) : ∀x : ℤ, f.func x = f.func 0 + (f.func 1 - f.func 0) * x := by
  intro n
  cases n
  rename_i n
  induction n with
  |zero =>
    simp
  |succ d hd =>
    simp; simp at hd
    let h := consecutive_d_same f d
    calc
      _ = f.func (d + 1) - f.func d + f.func d := by ring
      _ = f.func 1 - f.func 0 + f.func d := by rw [h]
      _ = (f.func 1 - f.func 0) + (f.func 0 + (f.func 1 - f.func 0) * d) := by rw [hd]
      _ = f.func 0 + (f.func 1- f.func 0) * (d + 1) := by ring
  rename_i n
  induction n with
  |zero =>
    simp
    let h := consecutive_dif_same f 0
    simp at h
    calc
      _ = f.func (-1) - f.func 0 + f.func 0 := by ring
      _ = -(f.func 0 - f.func (-1)) + f.func 0 := by ring
      _ = -(f.func 1 - f.func 0) + f.func 0 := by rw [h]
      _ = f.func 0 + (f.func 0 - f.func 1) := by ring
    |succ d hd =>
      simp at hd
      let h := consecutive_d_same f ((Int.negSucc d) - 1)
      ring_nf at h
      rw [add_comm] at h
      rw [←Int.sub_eq_add_neg] at h
      calc (f.func (Int.negSucc (Nat.succ d)))
        _ = f.func ((Int.negSucc d) - 1) := by simp
        _ = f.func ((Int.negSucc d) - 1) - f.func (Int.negSucc d) + f.func (Int.negSucc d) := by ring
        _ = -(f.func (Int.negSucc d) - f.func ((Int.negSucc d) - 1)) + f.func (Int.negSucc d) := by ring
        _ = -(f.func 1 - f.func 0) + (f.func 0 + (f.func 1 - f.func 0) * (Int.negSucc d)) := by rw [h, hd]
        _ = f.func 0 + (f.func 1 - f.func 0) * ((Int.negSucc d) - 1) := by ring
        _ = f.func 0 + (f.func 1 - f.func 0) * (Int.negSucc (d + 1)) := by simp

/-Proof that the inverse we defined is indeed the inverse-/
theorem inv_func_func_eq_self (f : IsometriesOverZ) : ∀ x, (inv_func f.func) (f.func x) = x := by
  intro x
  simp [inv_func]
  simp [generalFormIsometry f x]
  rw [←Int.mul_assoc (f.func 1 - f.func 0) (f.func 1 - f.func 0) x]
  have h : Int.natAbs (f.func 1 - f.func 0) = 1 := by
    let h1 := f.d_preserve 1 0
    simp [MyMetricSpace.d] at h1
    apply nat_to_real_inj at h1
    symm at h1
    exact h1
  simp [Int.natAbs_eq_iff] at h
  if h1 : (f.func 1 - f.func 0) = 1 then
    simp [h1]
  else
    simp [h1] at h
    simp [h]

/-Proof that the inverse we defined is surjective-/
theorem inv_func_surj (f : IsometriesOverZ) : ∀ y : Int, ∃ x, (inv_func f.func) x = y := by
  intro y
  exists f.func y
  exact inv_func_func_eq_self f y

/-With all 3 statements constructed, we can define the inverse of an  Isometry over ℤ-/
def inv : IsometriesOverZ → IsometriesOverZ
  | ⟨f, hd, hs⟩ => ⟨(inv_func f), (inv_func_d_preserve ⟨f, hd, hs⟩), (inv_func_surj ⟨f, hd, hs⟩)⟩


end IsometriesOverZ

/-The isometric isomorphisms form a group under comp and inv, with Id as the identity-/
instance IsometryGroupZ : MyGroup IsometriesOverZ where
  mul := MyIsometry.comp
  one := MyIsometry.Id
  inv := IsometriesOverZ.inv
  mul_assoc := by
    intro f g k
    have hf : f = ⟨f.func, f.d_preserve, f.func_sur⟩ := by rfl
    have hg : g = ⟨g.func, g.d_preserve, g.func_sur⟩ := by rfl
    have hk : k = ⟨k.func, k.d_preserve, k.func_sur⟩ := by rfl
    rw [hf, hg, hk]
    simp [MyIsometry.comp]
    have h : (f.func ∘ g.func) ∘ k.func = f.func ∘ (g.func ∘ k.func) := by rfl
    simp [h]
  mul_one := by
    simp [MyIsometry.Id]
    intro g
    have hg : g = ⟨g.func, g.d_preserve, g.func_sur⟩ := by rfl
    rw [hg]
    simp [MyIsometry.comp]
    have h : g.func ∘ (fun x => x) = g.func := by rfl
    simp [h]

  one_mul := by
    simp [MyIsometry.Id]
    intro g
    have hg : g = ⟨g.func, g.d_preserve, g.func_sur⟩ := by rfl
    rw [hg]
    simp [MyIsometry.comp]
    have h : (fun x => x) ∘ g.func = g.func := by rfl
    simp [h]

  inv_left_mul := by
    intro g
    have hg : g = ⟨g.func, g.d_preserve, g.func_sur⟩ := by rfl
    rw [hg]
    simp [IsometriesOverZ.inv, MyIsometry.comp, MyIsometry.Id]
    have h : (IsometriesOverZ.inv_func g.func) ∘ g.func = fun x => x := by
      simp [Function.comp, IsometriesOverZ.inv_func_func_eq_self]
    simp [h]

example {G : MyGroup IsometriesOverZ} (f : IsometriesOverZ) : f * f⁻¹ = 1 := by
  exact G.inv_right_mul f

example {G : MyGroup IsometriesOverZ} (f g : IsometriesOverZ) : (f * g)⁻¹ = g⁻¹ * f⁻¹ := by
  exact G.mul_inv_dist f g
