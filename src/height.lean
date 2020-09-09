import data.list tactic defs single

@[simp]
lemma height_ge1 : ∀ t : bintree, height t ≥ 1 :=
begin
  intros t, 
  destruct t, 
  repeat { 
    try {intros t H}, try {intros H}, rewrite H, repeat { unfold height }, omega
  }
end

@[simp]
lemma height_ne0 : ∀ t : bintree, ¬(height t = 0) :=
begin
  intros t contra,
  have ht : height t ≥ 1 := by simp,
  rewrite contra at ht, cases ht
end

@[simp]
lemma height_nle0 : ∀ t : bintree, ¬(height t ≤ 0) := 
begin
  intros t contra,
  have ht : height t = 0, omega, 
  eapply height_ne0, assumption
end

meta def pos_height : tactic unit := 
do
  tactic.exfalso,
  tactic.try (
    do tactic.eapplyc `height_ne0,
       tactic.assumption
  ),
  tactic.try (
    do tactic.eapplyc `height_nle0,
       tactic.assumption
  )

lemma height_le1_single : ∀ t : bintree, height t ≤ 1 → t = ● :=
begin
  intros t h1, 
  have h2 : height t ≥ 1, simp, 
  have ht : height t = 1, omega, 
  cases t,
  trivial, 
  repeat {
    unfold height at ht, have ht' : height t = 0, omega,
    pos_height, 
  },
  begin
    unfold height at ht, have ht' : max (height t_a) (height t_a_1) = 0, omega, 
    have ht'' : height t_a ≤ max (height t_a) (height t_a_1), apply le_max_left,
    rewrite ht' at ht'', 
    pos_height,
  end
end

lemma grow_height : ∀ t' t : bintree, (t ↣ t') → height t ≤ height t' :=
begin
  intros t', induction t',
  begin -- single 
    intros, unfold height, 
    rewrite (single_grow _ a), unfold height
  end,
  begin -- left 
    intros t h1,  
    cases t, 
    begin unfold height, apply ge.le, omega, end,
    begin 
      unfold height, 
      have h2 : (t ↣ t'_a), cases h1, repeat {assumption}, 
      simp, apply t'_ih, assumption
    end,
    repeat {cases h1}, 
  end,
  begin -- right
    intros t h1, 
    cases t, 
    begin unfold height, apply ge.le, omega, end, 
    cases h1,
    begin
      unfold height, 
      have h2 : (t ↣ t'_a), cases h1, repeat {assumption}, 
      simp, apply t'_ih, assumption
    end,
    cases h1
  end,
  begin -- full
    intros t h1, 
    cases t, 
    begin unfold height, omega end,
    cases h1, 
    cases h1, 
    begin
      unfold height, cases h1, 
      have h3 : height t_a ≤ height t'_a, apply t'_ih_a, assumption,
      have h3' : height t_a_1 ≤ height t'_a_1, apply t'_ih_a_1, assumption,
      have h4 : max (height t_a) (height t_a_1) ≤ max (height t'_a) (height t'_a_1), apply max_le_max, repeat {assumption}, 
      omega
    end
  end
end

lemma iso_height : ∀ t t' : bintree, (t = t') → height t = height t' :=
begin
  intros, rewrite a
end

lemma height_neq_niso : ∀ t t' : bintree, height t ≠ height t' → t ≠ t' :=
begin
  intros, intro contra, apply a, rewrite contra
end 

@[simp]
def height_bound : list bintree → ℕ
| [] := 1
| (t :: l) := max (height t) (height_bound l)

lemma height_bound_correct : ∀ l t, t ∈ l → height t ≤ height_bound l :=
begin
  intros l t h,
  induction l, 
  begin cases h end,
  begin
    unfold height_bound,
    cases h, 
    begin rewrite h, apply le_max_left end,
    begin
      eapply le_trans,
      apply l_ih, assumption, 
      apply le_max_right
    end
  end
end

lemma height_bound_ge1 : ∀ l, height_bound l ≥ 1 :=
begin
  intros l, 
  induction l,
  unfold height_bound, omega,
  unfold height_bound, eapply ge_trans, 
  begin apply has_le.le.ge, apply le_max_right end,
  begin assumption end
end

