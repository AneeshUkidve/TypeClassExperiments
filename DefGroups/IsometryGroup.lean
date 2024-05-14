import Mathlib
import DefGroups.MyGroups

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


@[ext]
structure MyIsometry {α : Type*} (inst : MyMetricSpace α) where
  func : α → α
  d_preserve : ∀ x y : α, inst.d x y = inst.d (func x) (func y)
  func_sur : ∀ y : α, ∃ x : α, func x = y

namespace MyIsometry


theorem comp_eq_d_preserve {α : Type*} [M : MyMetricSpace α] (f g : α → α) (hdf : ∀ x y : α, M.d x y = M.d (f x) (f y)) (hdg : ∀ x y : α, M.d x y = M.d (g x) (g y)) :
  ∀ x y : α, M.d x y = M.d ((f ∘ g) x) ((f ∘ g) y) := by
  intro x y
  simp [Function.comp]
  calc M.d x y
    _ = M.d (g x) (g y) := by apply hdg
    _ = M.d (f (g x)) (f (g y)) := by apply hdf

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

theorem func_inj {α : Type*} [M : MyMetricSpace α] (f : MyIsometry M) (x y : α) (h : f.func x = f.func y) : x = y := by
  apply M.eq_imp_d_zero at h
  rw [←f.d_preserve] at h
  rw [M.pos_def] at h
  exact h

/-
Could not define Inverses, got confused with noncomputable defs, could not
make it work.
-/


def comp {α : Type*} [M : MyMetricSpace α] : MyIsometry M → MyIsometry M → MyIsometry M
  | mk f hdf hsf, mk g hdg hsg => mk (f ∘ g) (comp_eq_d_preserve f g hdf hdg) (comp_eq_surj f g hsf hsg)

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
  2) The Isometries of it from a group under composition
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

def IsometricZ := MyIsometry MetricZ

namespace IsometricZ

def inv_func : (Int → Int) → (Int → Int)
  | f => fun x => ((f 1) - (f 0)) * (x - f 0)


theorem inv_func_d_preserve (f : IsometricZ) :
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


theorem consecutive_dif_same (f : IsometricZ) (d : ℤ) : f.func (d + 1) - f.func d = f.func d - f.func (d - 1) := by
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

theorem consecutive_d_same (f : IsometricZ) : ∀ n : Int, f.func (↑n + 1) - f.func (↑n) = (f.func 1 - f.func 0) := by
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




theorem inv_func_func_eq_self (f : IsometricZ) : ∀ x, (inv_func f.func) (f.func x) = x := by
  intro x
  cases x
  rename_i n
  induction n with
  |zero =>
    simp
    simp [inv_func]
  |succ d hd =>
    simp at hd
    simp
    simp [inv_func] at hd
    simp [inv_func]
    calc
      _ = (f.func 1 - f.func 0) * ((f.func (↑d + 1) - f.func (↑d)) + (f.func (↑d) - f.func 0)) := by simp
      _ = (f.func 1 - f.func 0) * (f.func (↑d + 1) - f.func (↑d)) + (f.func 1 - f.func 0) * (f.func (↑d) - f.func 0) := by rw [mul_add]
      _ = (f.func 1 - f.func 0) * (f.func (↑d + 1) - f.func (↑d)) + ↑d := by rw [hd]
      _ = ↑d + (f.func 1 - f.func 0) * (f.func (↑d + 1) - f.func (↑d)) := by rw [add_comm]
    sorry
  sorry


theorem inv_func_surj (f : IsometricZ) : ∀ y : Int, ∃ x, inv_func (f.func x) = y := by
  intro y
  exists f.func y
  sorry

end IsometricZ

instance : MyGroup IsometricZ where
  mul := MyIsometry.comp
  one := MyIsometry.Id/-Combine all three results to create function inverse which takes
an Isometry to another-/

  inv := sorry
  mul_assoc := sorry
  mul_one := sorry
  one_mul := sorry
  inv_right_mul := sorry
