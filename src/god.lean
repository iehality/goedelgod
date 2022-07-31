import ml

universes u v

namespace goedelgod
open ml kripke_frame
variables {F : kripke_frame.{u}} [S5 F]

constants {α : Type v} (positive : (α → F.prop) → F.prop)
variables (φ ψ : α → F.prop)

axiom axiom1 : ⊧ positive (λ x, ¬ₘφ x) ⟷ ¬ₘpositive φ
-- 任意の性質は肯定的(positive)か肯定的でないかのいずれかである

axiom axiom2 (φ ψ : α → F.prop) : ⊧ positive φ ⟶ (□ ∀ₘ x, φ x ⟶ ψ x) ⟶ positive ψ
-- φが肯定的なとき、必然的にφから導かれる性質は肯定的性質である

lemma false_negative : ⊧ ¬ₘpositive (λ x : α, (⊥ₘ : F.prop)) := λ w,
begin
  have : positive (λ x : α, ⊥ₘ) w ∨ (¬ₘpositive (λ x : α, ⊥ₘ)) w, from em w,
  rcases this,
  { exfalso,
    have h₁ : ¬positive (λ x : α, ⊤ₘ) w,
    from ((axiom1 (λ x : α, (⊤ₘ : F.prop))) w).1 (by simpa[mnot, mverum] using this ),
    have h₂ : positive (λ x : α, ⊤ₘ) w,
    from axiom2 (λ x : α, (⊥ₘ : F.prop)) (λ x, ⊤ₘ) w this (λ v hv x, by simp[mverum, (⟶)]),
    exact h₁ h₂ },
  { exact this }
end

theorem theorem1 : ⊧ positive φ ⟶ ◇∃ₘ x, φ x := λ w h,
begin
  have : (¬ₘpositive (λ x : α, ⊥ₘ) ⟶ ¬ₘ(□∀ₘ x, φ x ⟶ ⊥ₘ)) w,
    from mt (axiom2 φ (λ x : α, (⊥ₘ : F.prop)) w h),
  have : (◇∃ₘ x, ¬ₘ(φ x ⟶ ⊥ₘ)) w,
    by simpa[mnot_mbox_eq, mnot_mforall_eq] using (this $ false_negative w),
  simpa[mnot, mimplies, mfalsum] using this,
end
-- 肯定的な性質は満たされうる

def godlike : α → F.prop := λ x, ∀ₘ φ, positive φ ⟶ φ x
-- 神的(God-Like)であるとはあらゆる肯定的な性質を持つことである

axiom axiom3 : ⊧ positive (godlike : α → F.prop)
-- 神的な性質は肯定的である

theorem theorem2 : ⊧ (◇∃ₘ x : α, godlike x : F.prop) :=
λ w, theorem1 godlike w (axiom3 w)
-- 神的なものは存在しうる

def essence (φ : α → F.prop) (x : α) : F.prop := φ x ∧ₘ ∀ₘ (ψ : α → F.prop), ψ x ⟶ □∀ₘ y, φ y ⟶ ψ y
infix ` ess `:80 := essence
-- xがφを満たし、xについて成り立つあらゆる性質がφから必然的に導かれるものに限るとき、xはφの本質(essence)であるという

axiom axiom4 : ⊧ positive φ ⟶ □positive φ
-- 肯定的な性質は必然的に肯定的である

theorem theorem3 : ⊧ ∀ₘ x : α, (godlike x : F.prop) ⟶ godlike ess x :=
λ w x hg,
begin
  refine ⟨hg, λ ψ hψ v hv y hy, _⟩,
  have : positive ψ w,
  { by_contradiction A,
    have : (positive (λ x, ¬ₘψ x)) w, from (axiom1 ψ w).mpr A,
    have : ¬ψ x w, from hg (λ x, ¬ₘψ x) this,
    contradiction },
  have : positive ψ v, from axiom4 ψ w this v hv,
  exact hy ψ this
end
-- 神的なものは神性の本質である

def necessary_existence (x : α) : F.prop := ∀ₘ φ, φ ess x ⟶ □∃ₘ y, φ y
-- xが本質であるようなあらゆる性質が必然的に満たされる時、xは必然的存在(Necessary existence)である

axiom axiom5 : ⊧ positive (necessary_existence : α → F.prop)
-- 本質的存在性は肯定的である

theorem theorem4 : ⊧ □∃ₘ x : α, (godlike x : F.prop) :=
begin
  have : ⊧ ◇□∃ₘ x : α, (godlike x : F.prop),
  { intros w,
    have : (◇∃ₘ x, godlike x) w, from (theorem2 : ⊧ ◇∃ₘ x : α, (godlike x : F.prop)) w,
    rcases this with ⟨v, hv, x, gv⟩,
    have nv : necessary_existence x v, from gv (necessary_existence : α → F.prop) (axiom5 v),
    have : (□∃ₘ y, godlike y) v, from nv godlike (theorem3 v x gv),
    refine ⟨v, hv, this⟩ },
  exact λ w, dia_box_implies_box w (this w)
end
-- 神的なものは必然的に存在する

theorem modal_collapse {φ : F.prop} : ⊧ φ ⟷ □φ := λ w,
⟨λ hw v rv,
  begin
    have T4w : ∃ x : α, godlike x w, from theorem4 w w (T.reflexivity w),
    have T4v : ∃ x : α, godlike x v, from theorem4 w v rv,
    rcases T4v with ⟨x, T4v⟩,  
    have : (∃ x : α, godlike x w) → (φ ⟶ □∀ₘ y : α, godlike y ⟶ φ) w,
    { rintros ⟨x, hw⟩, simpa using (theorem3 w x hw).2 (λ _, φ)},
    exact this T4w hw v rv x T4v
  end, box_implies w⟩
-- そんな...

end goedelgod