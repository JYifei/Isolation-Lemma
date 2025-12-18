theory Perfect_Matching_Parallel
  imports
    Main 
    "HOL-Analysis.Determinants"
    "HOL-Number_Theory.Number_Theory"
    "Isolation_Lemma_Main"
begin

locale bipartite_graph = 
  fixes n :: nat
  fixes w :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  fixes E :: "(nat \<times> nat) set"

begin
definition D_entry :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "D_entry i j = (if (i,j) \<in> E then (2::int) ^ (w i j) else 0)"

definition det_D :: int where
  "det_D = (\<Sum>p \<in> {p. p permutes{0..<n}}. sign p * (\<Prod>i = 0..<n. D_entry i (p i)))"

definition is_perfect_matching :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_perfect_matching p \<longleftrightarrow> (p permutes{0..<n} \<and> (\<forall>i < n. (i, p i) \<in> E))"

definition matching_weight :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "matching_weight p = (\<Sum>i = 0..<n. w i (p i))"

definition min_weight_val :: nat where
  "min_weight_val = Min {matching_weight p | p. is_perfect_matching p}"

definition unique_min_weight_condition :: bool where
  "unique_min_weight_condition \<longleftrightarrow>
  (\<exists>! p. is_perfect_matching p \<and> matching_weight p = min_weight_val)"


lemma term_value_zero:
  assumes "p permutes{0..<n}"
  assumes "\<not>is_perfect_matching p"
  shows "(\<Prod>i = 0..<n. D_entry i (p i)) = 0"
proof -
  obtain i where "i < n" and "(i, p i) \<notin> E"
    using assms is_perfect_matching_def by auto

  hence "D_entry i(p i) = 0"
    unfolding D_entry_def by auto

  then show ?thesis
    using \<open>i < n\<close> by auto
qed

lemma term_value_non_zero:
  assumes "p permutes{0..<n}"
  assumes "is_perfect_matching p"
  shows "abs (\<Prod>i = 0..<n. D_entry i (p i)) = (2::int) ^ (matching_weight p)"
proof -
  have " (\<Prod>i = 0..<n. D_entry i (p i)) =  (\<Prod>i = 0..<n. (2::int)^ (w i (p i)))"
  proof (rule prod.cong)
    show "{0..<n} = {0..<n}" by simp
    fix i assume "i \<in> {0..<n}"
    have "i < n" using \<open>i \<in> {0..<n}\<close> by simp
    have "(i, p i) \<in> E" using assms \<open>i < n\<close>
      unfolding is_perfect_matching_def by auto
    then show "D_entry i (p i) = (2::int) ^ (w i (p i))"
      unfolding D_entry_def by simp
  qed

  also have "... = (2::int) ^ (\<Sum>i = 0..<n. w i(p i))"
    by (simp add: power_sum) 

  also have "... = (2::int) ^ (matching_weight p)"
    unfolding matching_weight_def by auto

  finally show ?thesis by auto
qed


lemma multiplicity_2_abs:
  fixes x :: int
  assumes "abs x = 2 ^ k"
  shows "multiplicity 2 x = k"
  using assms
  by (smt (verit, best) abs_of_nonpos dvd_abs_iff multiplicity_cong
      multiplicity_same_power zdvd1_eq)

lemma finite_perfect_matchings: "finite {p. is_perfect_matching p}"
proof -
  have "finite {0..<n}" by simp

  then have "finite {p. p permutes {0..<n}}"
    by (simp add: finite_permutations)

  moreover have "{p. is_perfect_matching p} \<subseteq>  {p. p permutes {0..<n}}"
    by (simp add: Collect_mono is_perfect_matching_def)

  ultimately show ?thesis
    using rev_finite_subset by blast
qed


lemma minimum_weight:
  assumes "is_perfect_matching p"
  shows "matching_weight p \<ge> min_weight_val"
proof -
  have non_empty: "{matching_weight r | r. is_perfect_matching r} \<noteq> {}"
    using assms by blast

  have finite_set: "finite {matching_weight r | r. is_perfect_matching r}"
    using finite_perfect_matchings by simp

  have "min_weight_val = Min {matching_weight r | r. is_perfect_matching r}" 
    unfolding min_weight_val_def by simp

  moreover have "matching_weight p \<in> {matching_weight r | r. is_perfect_matching r}"
    using assms by auto

  ultimately show ?thesis
    by (simp add:
        \<open>finite {matching_weight r |r. is_perfect_matching r}\<close>)
qed

lemma multiplicity_2_not_dvd_Suc:
  fixes x :: int and k :: nat
  assumes hk: "multiplicity (2::int) x = k"
    and hx: "x \<noteq> 0"
  shows "\<not> (2::int) ^ (k + 1) dvd x"
proof
  assume h: "(2::int) ^ (k + 1) dvd x"
  have "k+1 \<le> multiplicity (2::int) x"
    using h multiplicity_2_abs
    by (simp add: hx multiplicity_geI)
  thus False
    by (simp add: hk)
qed


(*1. Calculate det_D*)
(*Case 1: No Perfect Matching Case*)
lemma no_perfect_matching_det_0:
  assumes "\<nexists>p. is_perfect_matching p"
  shows "det_D = 0"
proof -
  have term_zero: "\<forall>p. p permutes{0..<n} \<longrightarrow>( \<Prod>i=0..<n. D_entry i(p i)) = 0"
  proof (intro allI impI)
    fix p assume "p permutes {0..<n}"
    have "\<not>is_perfect_matching p"
      using assms by auto
    then show "(\<Prod>i = 0..<n. D_entry i (p i)) = 0"
      using `p permutes {0..<n}` term_value_zero by simp
  qed
  have "(\<Sum>p \<in> {p. p permutes{0..<n}}. sign p * (\<Prod>i = 0..<n. D_entry i (p i))) = 0"
    by (simp add: term_zero)
  then show ?thesis
    unfolding det_D_def by auto
qed


(*Case 2: One Perfect Matching Case with Unique Minimum Weight Exists*)
lemma unique_det_power_of_weight:
  assumes "unique_min_weight_condition"
  shows "multiplicity 2 det_D = min_weight_val"
proof -
  obtain p_min where p_min_props:
    "is_perfect_matching p_min"
    "matching_weight p_min = min_weight_val"
    "\<forall>q. is_perfect_matching q \<and> matching_weight q = min_weight_val \<longrightarrow> q = p_min"
  proof -
    have "\<exists>! p. is_perfect_matching p \<and> matching_weight p = min_weight_val"
      using assms unique_min_weight_condition_def by auto
    then show ?thesis 
      using that by blast
  qed


  let ?S_all = "{p. p permutes {0..<n}}"
  let ?S_other = "?S_all - {p_min}"
  have split_sum : "det_D = (sign p_min * (\<Prod>i = 0..<n. D_entry i (p_min i))) +
                            (\<Sum>p \<in> ?S_other. sign p * (\<Prod>i = 0..<n. D_entry i (p i)))"
  proof - 
    have p_in_S: "p_min \<in> ?S_all"
      using p_min_props(1) 
      unfolding is_perfect_matching_def by simp

    have S_finite: "finite ?S_all"
      using finite_permutations by auto

    show ?thesis
      unfolding det_D_def
      by (metis (mono_tags, lifting) S_finite
          insert_absorb p_in_S sum.insert_remove)
  qed

  have val_min: "multiplicity 2  (sign p_min * (\<Prod>i = 0..<n. D_entry i (p_min i))) = min_weight_val"
    proof -
    have perm_min: "p_min permutes {0..<n}"
      using p_min_props(1) unfolding is_perfect_matching_def by auto

    have abs_prod:
      "abs (\<Prod>i = 0..<n. D_entry i (p_min i)) = (2::int) ^ min_weight_val"
      using p_min_props(1,2) perm_min term_value_non_zero
      by presburger

    have sign_pm1: "sign p_min = (1::int) \<or> sign p_min = -1"
      using sign_cases by blast

    have abs_term:
      "abs (sign p_min * (\<Prod>i = 0..<n. D_entry i (p_min i))) = (2::int) ^ min_weight_val"
      using abs_prod sign_pm1 by force 

    show ?thesis
      using abs_term multiplicity_2_abs by blast
  qed


  have min_dvd_other: "2 ^ (min_weight_val + 1) dvd (\<Sum>p \<in> ?S_other. sign p * (\<Prod>i = 0..<n. D_entry i (p i)))"
  proof -
    have each_term_divisible:
      "\<forall>p \<in> ?S_other. (2::int) ^ (min_weight_val + 1) dvd (sign p * (\<Prod>i = 0..<n. D_entry i (p i)))"
    proof
      fix p
      assume p_in_other: "p \<in> ?S_other"

      show "(2::int) ^ (min_weight_val + 1) dvd (sign p * (\<Prod>i = 0..<n. D_entry i (p i)))"
      proof(cases "is_perfect_matching p")
        case False
        then have prod_zero: "(\<Prod>i=0..<n. D_entry i (p i)) = 0"
          using p_in_other term_value_zero by auto
        then show ?thesis
          by (metis dvd_0_right mult_zero_right) 
      next
        case True
        have perm_p: "p permutes {0..<n}"
          using True is_perfect_matching_def by auto

        have weight_greater: "matching_weight p > min_weight_val"
        proof -
          have p_not_pmin: "p \<noteq> p_min"
            using p_in_other by blast

          have weight_neq_min: "matching_weight p \<noteq> min_weight_val"
            using True p_min_props(3) p_not_pmin by auto 

          have weight_greater_min: "matching_weight p \<ge> min_weight_val"
            by (simp add: True minimum_weight)
            

          then show ?thesis
            using weight_neq_min by auto 
        qed

        then have weight_lower_bound: "matching_weight p \<ge> min_weight_val + 1"
          by simp

        have abs_prod: "abs (\<Prod>i=0..<n. D_entry i (p i)) = (2::int) ^ (matching_weight p)"
          using True perm_p term_value_non_zero by blast          

        have abs_term: "abs (sign p * (\<Prod>i=0..<n. D_entry i (p i))) = (2::int) ^ (matching_weight p)"
        proof -
          have  "abs (sign p * (\<Prod>i=0..<n. D_entry i (p i))) = abs (sign p) * abs (\<Prod>i=0..<n. D_entry i (p i))"
            using abs_mult by blast 
          also have "... = 1 * abs (\<Prod>i=0..<n. D_entry i (p i))"
            by (metis abs_1 abs_zmult_eq_1 sign_idempotent)
          also have "... = abs (\<Prod>i=0..<n. D_entry i (p i))"
            by simp
          also have "... = (2::int) ^ (matching_weight p)"
            by (simp add: local.abs_prod) 
          finally show ?thesis
            by auto 
          qed
            
        have power_divides: "(2::int) ^ (matching_weight p) dvd (sign p *(\<Prod>i=0..<n. D_entry i (p i)))"
          by (metis abs_term dvd_abs_iff dvd_refl)
          

        have power_inequality: "(2::int) ^  (min_weight_val + 1) dvd (sign p *(\<Prod>i=0..<n. D_entry i (p i)))"
          using power_divides power_le_dvd weight_lower_bound by blast
         

        then show ?thesis
          by blast
      qed
    qed

    show ?thesis
      using dvd_sum each_term_divisible by fastforce
  qed


  have det_multiplicity: 
    "multiplicity 2 det_D = min_weight_val"
  proof -
    let ?A = "(sign p_min * (\<Prod>i = 0..<n. D_entry i (p_min i)))"
    let ?B = "(\<Sum>p \<in> ?S_other. sign p * (\<Prod>i = 0..<n. D_entry i (p i)))"
    let ?k = "min_weight_val"

    have A_nonzero: "?A \<noteq> 0"
    proof
      assume h0: "?A = 0"
      hence "abs ?A = 0" by simp
      moreover have "(2::int)^?k \<noteq> 0" by simp
      ultimately show False
        by (metis
            \<open>\<And>thesis. (\<And>p_min. is_perfect_matching p_min \<Longrightarrow> matching_weight p_min = min_weight_val \<Longrightarrow> \<forall>q. is_perfect_matching q \<and> matching_weight q = min_weight_val \<longrightarrow> q = p_min \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
            bipartite_graph.is_perfect_matching_def h0 mult_eq_0_iff
            p_min_props(3) sign_nz term_value_non_zero) 
    qed

    have det_split: "det_D = ?A + ?B"
      using split_sum by blast

    have dvd_k: "(2::int) ^ ?k dvd det_D"
    proof -
      have "(2::int) ^ ?k dvd ?A"
        by (metis multiplicity_dvd val_min)
      have "(2::int) ^ ?k dvd ?B"
        using min_dvd_other by auto
      then have "(2::int) ^ ?k dvd ?A + ?B"
        using
          \<open>2 ^ min_weight_val dvd (\<Sum>p\<in>{p. p permutes {0..<n}} - {p_min}. sign p * (\<Prod>i = 0..<n. D_entry i (p i)))\<close>
          \<open>2 ^ min_weight_val dvd sign p_min * (\<Prod>i = 0..<n. D_entry i (p_min i))\<close>
          dvd_add_right_iff by blast

      thus ?thesis
        by (metis split_sum) 
    qed

    have not_dvd_A_ge_k: "\<not>(2::int) ^ (?k + 1) dvd ?A"
      using multiplicity_2_not_dvd_Suc[OF val_min A_nonzero] .

    have not_dvd_ge_k: "\<not>(2::int) ^ (?k + 1) dvd det_D"
    proof
      assume hdet: "(2::int) ^ (?k + 1) dvd det_D"
      have hsum: "(2::int) ^ (?k + 1) dvd ?A + ?B"
        by (metis hdet split_sum)

      have hA: "(2::int) ^ (?k + 1) dvd ?A"
        using dvd_add_left_iff hsum min_dvd_other by blast

      show False
        using hA not_dvd_A_ge_k by auto 
    qed

    have not_dvd_suc: "\<not> (2::int) ^ Suc ?k dvd det_D"
      using not_dvd_ge_k by simp

    show ?thesis 
      using dvd_k not_dvd_suc
      by (rule multiplicity_eqI)
  qed

  show ?thesis
    by (simp add: det_multiplicity)
qed

(*Case 3: More Than One Perfect Matching Case with Unique Minimum Weight Exists*)

(*2. Edge Isolation Logic*)
(*We want to show the parallel algorithm correct,
  Which is, 
  1. Find the minimum weight W_0
  2. Find an arbitrary edge, check: 
      a. Minimum weight of D_i_j 
      b. Weight of edge i j
     if D_i_j + W i_j = W_0, then edge i j is in the perfect match*)

definition matching_with_edge :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "matching_with_edge i j = {p. is_perfect_matching p \<and> p i = j}"

definition minor_sum :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "minor_sum i j = (\<Sum>p \<in> matching_with_edge i j. sign p * (\<Prod>k = 0..<n. D_entry k (p k)))"

definition cofactor_sum :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "cofactor_sum i j = (\<Sum>p \<in>  matching_with_edge i j. sign p * (\<Prod>k \<in> {0..<n} - {i}. D_entry k (p k)))"


lemma minor_sum_decomposition:
  assumes "i<n" "j<n" "(i,j) \<in> E"
  shows "minor_sum i j = D_entry i j * cofactor_sum i j"
  sorry






lemma sum_eq_implies_correct:
  fixes p_min :: "nat \<Rightarrow> nat" and i j :: nat

  assumes "unique_min_weight_condition"
  assumes p_min_def: "is_perfect_matching p_min" 
          "matching_weight p_min = min_weight_val"
  assumes p_min_unique: "\<forall>q. is_perfect_matching q \<and>
                          matching_weight q = min_weight_val 
                          \<longrightarrow> q = p_min"

  assumes edge_exists: "(i, j) \<in> E"
  assumes i_valid: "i < n" and j_valid: "j < n"

  assumes sum_eq: "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"

  shows "p_min i = j"
proof -

  show ?thesis
    sorry
qed


lemma correct_implies_sum_eq:
  fixes p_min :: "nat \<Rightarrow> nat" and i j :: nat

  assumes "unique_min_weight_condition"
  assumes p_min_def: "is_perfect_matching p_min" 
          "matching_weight p_min = min_weight_val"
  assumes p_min_unique: "\<forall>q. is_perfect_matching q \<and>
                          matching_weight q = min_weight_val 
                          \<longrightarrow> q = p_min"

  assumes edge_exists: "(i, j) \<in> E"
  assumes i_valid: "i < n" and j_valid: "j < n"

  assumes correct_edge: "p_min i = j"

  shows "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
proof -

  show ?thesis
    sorry
qed







theorem edge_test_iff_correct:
  fixes p_min :: "nat \<Rightarrow> nat" and i j :: nat
  assumes "unique_min_weight_condition"
  assumes p_min_def: "is_perfect_matching p_min" 
          "matching_weight p_min = min_weight_val"
  assumes p_min_unique: "\<forall>q. is_perfect_matching q \<and>
                          matching_weight q = min_weight_val 
                          \<longrightarrow> q = p_min"
  assumes edge_exists: "(i, j) \<in> E"
  assumes i_valid: "i < n" and j_valid: "j < n"
  shows "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val \<longleftrightarrow> p_min i = j"

proof (rule iffI)
  assume "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
  show "p_min i = j"
    sorry

next
  assume "p_min i = j"
  show "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
    sorry
qed

end

end

