import Mathlib

structure poset1 (α : Type*) where
  le : α → α → Prop
  le_refl : ∀ x : α, le x x = True
  le_anti_symm : ∀ x y : α , ((le x y) ∧ (le y x)) → x = y
  le_trans : ∀ x y z : α, le x y ∧ le y z → le x z

def setNatPoset : poset1 (Set ℕ) where
  le := Set.Subset
  le_refl := by simp [Set.Subset]
  le_anti_symm := by
    intro x y h
    have h1 : Set.Subset x y := And.left h
    have h2 : Set.Subset y x := And.right h
    exact Set.Subset.antisymm h1 h2
  le_trans := by
    intro x y z h
    have h1 : Set.Subset x y := And.left h
    have h2 : Set.Subset y z := And.right h
    exact Set.Subset.trans h1 h2

theorem lower_bound : ∃ zero : Set Nat, ∀ (a : Set Nat), setNatPoset.le zero a := by
  exists ∅
  intro a
  simp [setNatPoset]
  simp [Set.Subset]

theorem upper_bound : ∃ one : Set Nat, ∀ (a : Set Nat), setNatPoset.le a one := by
  exists Set.univ
  simp [setNatPoset]
  simp [Set.Subset]

structure bounded_poset (α : Type*) extends poset1 α where
  one : α
  zero : α
  zero_le : ∀ x : α, le zero x
  le_one : ∀ x : α, le x one
