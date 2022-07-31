import tactic
open classical

universes u v

attribute [instance, priority 0] classical.prop_decidable

structure kripke_frame :=
(world : Type u)
(rel : world → world → Prop)

variables (F : kripke_frame) {α : Type*}

namespace kripke_frame

class T := (reflexivity : ∀ w, F.rel w w)

class B := (symmetry : ∀ {w v}, F.rel w v → F.rel v w)

class Four := (transitive : ∀ {w v u}, F.rel w v → F.rel v u → F.rel w u)

class S5 extends T F, B F, Four F

instance : has_coe_to_sort kripke_frame (Type*) := ⟨kripke_frame.world⟩

abbreviation prop := set F

variables {F}
def mverum : F.prop := λ w, true
notation `⊤ₘ` := mverum

def mfalsum : F.prop := λ w, false
notation `⊥ₘ` := mfalsum

def mnot : F.prop → F.prop := λ φ w, ¬φ w
prefix `¬ₘ`:70 := mnot

def mand : F.prop → F.prop → F.prop := λ φ ψ w, φ w ∧ ψ w
infixl ` ∧ₘ `:67 := mand

def mor : F.prop → F.prop → F.prop := λ φ ψ w, φ w ∨ ψ w
infixl ` ∨ₘ `:66 := mor

def mimplies : F.prop → F.prop → F.prop := λ φ ψ w, φ w → ψ w
infixr ` ⟶ `:65 := mimplies

def miff : F.prop → F.prop → F.prop := λ φ ψ w, φ w ↔ ψ w
infix ` ⟷ `:60 := miff

def mforall : Π {α}, (α → F.prop) → F.prop := λ α φ w, ∀ x, φ x w 
notation `∀ₘ` binders `, ` r:(scoped p, mforall p) := r

def mexists : Π {α}, (α → F.prop) → F.prop := λ α φ w, ∃ x, φ x w 
notation `∃ₘ` binders `, ` r:(scoped p, mexists p) := r

def mbox : F.prop → F.prop := λ φ w, ∀ v, F.rel w v → φ v
prefix `□`:70 := mbox

def mdia : F.prop → F.prop := λ φ w, ∃ v, F.rel w v ∧ φ v
prefix `◇`:70 := mdia

def valid (φ : F.prop) : Prop := ∀ w, φ w
prefix `⊧ `:30 := valid

end kripke_frame

namespace ml
open kripke_frame
variables {F} {φ ψ : F.prop}

lemma mK {φ ψ : F.prop} : ⊧ □(φ ⟶ ψ) ⟶ □φ ⟶ □ψ :=
λ w h₁ h₂ v hv, h₁ v hv (h₂ v hv)

lemma mnot_mbox_eq {φ : F.prop} : ¬ₘ□φ = ◇¬ₘφ :=
funext (λ w, by simp[mnot, mbox, mdia])

lemma mnot_mforall_eq {φ : α → F.prop} : ¬ₘ(∀ₘ x, φ x) = ∃ₘ x, ¬ₘφ x :=
funext (λ w, by simp[mforall, mexists, mnot])

lemma em : ⊧ φ ∨ₘ ¬ₘφ := λ w, classical.em (φ w)

lemma N : (⊧ φ) → (⊧ □φ) := λ h w v hv, h v

theorem box_implies [T F] : ⊧ □φ ⟶ φ := λ w h, h w (T.reflexivity w)

theorem implies_box_dia [B F] : ⊧ φ ⟶ □◇φ := λ w h v hv, ⟨w, B.symmetry hv, h⟩

theorem box_implies_box_box [Four F] : ⊧ □φ ⟶ □□φ :=
λ w h v hv u hu, h u (Four.transitive hv hu)

theorem dia_box_implies_box [S5 F] : ⊧ ◇□φ ⟶ □φ :=
λ w ⟨v, hv, h⟩ u hu, by { have : F.rel v u, from Four.transitive (B.symmetry hv) hu, refine h u this }

end ml