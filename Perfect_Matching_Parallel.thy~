theory Perfect_Matching_Parallel
  imports
    Main 
    "HOL-Analysis.Determinants"
    "HOL-Number_Theory.Number_Theory"
    "Isolation_Lemma_Main"
    "Schwartz_Zippel.Rand_Perfect_Matching"
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

lemma terms_divisible_by_min_weight:
  shows "\<forall>p. p permutes {0..<n} \<longrightarrow> (2::int) ^ min_weight_val dvd (sign p * (\<Prod>i=0..<n. D_entry i (p i)))"
proof (intro allI impI)
  fix p assume perm: "p permutes {0..<n}"
  let ?term = "sign p * (\<Prod>i=0..<n. D_entry i (p i))"

  show "(2::int) ^ min_weight_val dvd ?term"
  proof (cases "is_perfect_matching p")
    case False
    then show ?thesis
      using term_value_zero perm
      by (metis even_mult_iff even_numeral mult_numeral_1_right
          power_eq_0_iff times_int_code(1) zdvd_mono
          zero_neq_numeral)
  next
    case True
    have ge: "matching_weight p \<ge> min_weight_val"
      by (simp add: True bipartite_graph.minimum_weight) 

    have abs_eq: "abs ?term = (2::int) ^ matching_weight p"
    proof -
      have "abs ?term = abs (sign p) * abs (\<Prod>i=0..<n. D_entry i (p i))"
        using abs_mult by blast
      also have "... = abs(sign p) * ((2::int) ^ matching_weight p)"
        using True perm term_value_non_zero by presburger
      also have "... = (2::int) ^ matching_weight p" by auto
      finally show ?thesis by simp
    qed

    have "(2::int) ^ min_weight_val dvd (2::int) ^ matching_weight p"
      using ge by (simp add: dvd_power_iff)

    then have "(2::int) ^ min_weight_val dvd abs ?term"
      using abs_eq by presburger

    then show ?thesis
      using dvd_abs_iff by blast

  qed
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
lemma not_unique_zero_or_min_weight:
  assumes "\<exists>p. is_perfect_matching p"
  shows "det_D = 0 \<or> multiplicity 2 det_D \<ge> min_weight_val"
proof -
  have all_div: "\<forall>p. p permutes{0..<n} \<longrightarrow> (2::int) ^ min_weight_val dvd (sign p * (\<Prod>i=0..<n. D_entry i (p i)))"
    using terms_divisible_by_min_weight by blast

  have dvd_total: "(2::int) ^ min_weight_val dvd det_D"
    unfolding det_D_def
    by (metis (no_types, lifting) all_div dvd_sum
        mem_Collect_eq)

  show ?thesis
  proof (cases "det_D = 0")
    case True then show ?thesis by simp
  next
    case False
    then show ?thesis
      by (simp add: dvd_total multiplicity_geI)
  qed
qed

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
proof - 
  have  "minor_sum i j = (\<Sum>p \<in> matching_with_edge i j. sign p * (\<Prod>k = 0..<n. D_entry k (p k)))"
    unfolding minor_sum_def by auto

  also have "... = (\<Sum>p \<in> matching_with_edge i j. D_entry i j *( sign p * (\<Prod>k \<in> {0..<n} - {i}. D_entry k (p k))))"
  proof (rule sum.cong)
    show "matching_with_edge i j = matching_with_edge i j" by simp
    fix p assume "p \<in> matching_with_edge i j"
    hence "p i = j" unfolding matching_with_edge_def by simp

    have "(\<Prod>k = 0..<n. D_entry k (p k)) = D_entry i (p i) * (\<Prod>k \<in> {0..<n} - {i}. D_entry k (p k))"
      apply (rule prod.remove)
      apply simp
      by (simp add: assms(1))

    hence "(\<Prod>k = 0..<n. D_entry k (p k)) = D_entry i j * (\<Prod>k \<in> {0..<n} - {i}. D_entry k (p k))"
      using \<open>p i = j\<close> by presburger

    thus "sign p * (\<Prod>k = 0..<n. D_entry k (p k)) = D_entry i j *(sign p * (\<Prod>k \<in> {0..<n} - {i}. D_entry k (p k)))"
      by simp 
  qed

  also have "... =  D_entry i j * (\<Sum>p \<in> matching_with_edge i j.(sign p * (\<Prod>k \<in> {0..<n} - {i}. D_entry k (p k))))"
    by (simp add: sum_distrib_left)

  also have "... = D_entry i j * cofactor_sum i j"
    unfolding cofactor_sum_def by simp

  finally show ?thesis .
qed





lemma unique_subset_sum_power_of_weight:
  fixes S :: "(nat \<Rightarrow> nat) set"
  assumes "finite S"
  assumes "p_min \<in> S"
  assumes p_min_pm: "is_perfect_matching p_min"
  assumes p_min_unique: "\<forall>q \<in> S - {p_min}. is_perfect_matching q \<longrightarrow> matching_weight q > matching_weight p_min"
  assumes S_permutes: "\<forall>p \<in> S. p permutes {0..<n}"
  shows sum_nonzero: "(\<Sum>p \<in> S. sign p * (\<Prod>k=0..<n. D_entry k (p k))) \<noteq> 0"
    and sum_multiplicity: "multiplicity 2 (\<Sum>p \<in> S. sign p * (\<Prod>k=0..<n. D_entry k (p k))) = matching_weight p_min"
proof -
  let ?w_min = "matching_weight p_min"
  let ?term = "\<lambda>p. sign p * (\<Prod>i = 0..<n. D_entry i(p i))"

  have sum_split: "(\<Sum>p \<in> S. ?term p) = ?term p_min + (\<Sum>p \<in> S - {p_min}. ?term p)"
    by (metis (mono_tags, lifting) assms(1,2) insert_absorb sum.insert_remove)

  have val_p_min: "multiplicity 2 (?term p_min) = ?w_min"
  proof -
    have "abs (?term p_min) = (2::int) ^ ?w_min"
    proof -
      have "p_min permutes {0..<n}"
        using assms(3) is_perfect_matching_def by blast
      thus ?thesis
        by (metis (lifting) abs_mult abs_zmult_eq_1 arith_simps(43) assms(3)
            bipartite_graph.term_value_non_zero mult_1s(1,2) mult_left_cancel
            pos_zmult_eq_1_iff sign_left_idempotent sign_nz zabs_less_one_iff)
    qed
    thus ?thesis using multiplicity_2_abs by blast
  qed

  have term_p_min_nonzero: "?term p_min \<noteq> 0"
  proof -
    have "p_min permutes {0..<n}" using p_min_pm is_perfect_matching_def by simp
    have "abs (?term p_min) = (2::int) ^ ?w_min"
      using p_min_pm term_value_non_zero abs_mult abs_sign mult_1
      by (metis \<open>p_min permutes {0..<n}\<close>)
    then have "abs (?term p_min) > 0" by simp
    thus ?thesis by simp
  qed

  have rest_divisible: "(2::int)^(?w_min + 1) dvd (\<Sum>p \<in> S - {p_min}. ?term p)"
  proof (rule dvd_sum)
    fix q assume q_in_rest: "q \<in> S - {p_min}"
    have "q \<in> S" using q_in_rest by blast
    show "(2::int) ^ (?w_min +1) dvd ?term q"
    proof (cases "is_perfect_matching q")
      case False
      have "q permutes {0..<n}" by (simp add: \<open>q \<in> S\<close> assms(5))
      then have "?term q = 0" by (simp add: False term_value_zero)
      then show ?thesis
        by (smt (verit, ccfv_threshold) even_zero mult_delta_right
            multiplicity_2_abs multiplicity_decomposeI multiplicity_zero
            odd_one power_0)
    next
      case True
      have "matching_weight q > ?w_min" using True p_min_unique q_in_rest by blast
      then have w_ge: "matching_weight q \<ge> ?w_min + 1" by simp
      have "q permutes {0..<n}" by (simp add: \<open>q \<in> S\<close> assms(5))
      then have "abs(?term q) = (2::int) ^ (matching_weight q)"
        using True term_value_non_zero abs_mult abs_sign mult_1 by metis
      then have "(2::int) ^ (matching_weight q) dvd ?term q"
        by (metis multiplicity_2_abs multiplicity_dvd)
      moreover have "(2::int) ^ (?w_min + 1) dvd (2::int) ^ (matching_weight q)"
        using le_imp_power_dvd w_ge by blast
      ultimately show ?thesis using dvd_trans by blast
    qed
  qed

  have not_dvd_sum: "\<not> (2::int)^(Suc ?w_min) dvd (\<Sum>p \<in> S. ?term p)"
  proof -
    have "\<not> (2::int) ^ (?w_min + 1) dvd ?term p_min"
      using multiplicity_2_not_dvd_Suc val_p_min term_p_min_nonzero by blast
    then show ?thesis
      unfolding sum_split using rest_divisible dvd_add_left_iff by auto
  qed

  show "(\<Sum>p \<in> S. ?term p) \<noteq> 0"
    using not_dvd_sum by auto

  show "multiplicity 2 (\<Sum>p \<in> S. ?term p) = ?w_min"
  proof (rule multiplicity_eqI)
    show "(2::int) ^ ?w_min dvd (\<Sum>p \<in> S. ?term p)"
    proof -
      have "(2::int) ^ ?w_min dvd ?term p_min" by (metis multiplicity_dvd val_p_min)
      moreover have "(2::int) ^ ?w_min dvd (\<Sum>p \<in> S - {p_min}. ?term p)"
        using rest_divisible power_le_dvd le_add1 by blast
      ultimately show ?thesis 
        using sum_split by (metis (no_types, lifting) dvd_add)
    qed
  next
    show "\<not> (2::int) ^(Suc ?w_min) dvd (\<Sum>p \<in> S. ?term p)"
      using not_dvd_sum by simp
  qed
qed

lemma sum_eq_implies_correct_edge:
  fixes p_min :: "nat \<Rightarrow> nat" and i j :: nat
  assumes p_min_def: "is_perfect_matching p_min" 
          "matching_weight p_min = min_weight_val"
  assumes p_min_unique: "\<forall>q. is_perfect_matching q \<and>
                          matching_weight q = min_weight_val 
                          \<longrightarrow> q = p_min"

  assumes edge_exists: "(i, j) \<in> E"
  assumes i_valid: "i < n" and j_valid: "j < n"

  assumes sum_eq: "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
  assumes cofactor_nz: "cofactor_sum i j \<noteq> 0"

  shows "p_min i = j"
proof (rule ccontr)
  assume neq: "p_min i \<noteq> j"
  let ?S = "matching_with_edge i j"

  have S_nonempty: "?S \<noteq> {}"
  proof -
    have "minor_sum i j = D_entry i j * cofactor_sum i j"
      by (simp add: assms(4,5,6) minor_sum_decomposition)
    then have "minor_sum i j \<noteq> 0"
      using cofactor_nz unfolding D_entry_def using edge_exists by simp
    then show ?thesis unfolding minor_sum_def by auto
  qed

  have S_finite: "finite ?S"
    by (simp add: bipartite_graph.finite_perfect_matchings
        matching_with_edge_def)

  obtain q_best where q_best_props:
    "q_best \<in> ?S"
    "\<forall>q \<in> ?S. matching_weight q \<ge> matching_weight q_best"
  proof -
    let ?W = "matching_weight ` ?S"
    have "finite ?W" by (simp add: S_finite)
    moreover have "?W \<noteq> {}" using S_nonempty by simp
    ultimately have "Min ?W \<in> ?W" by (rule Min_in)

    then obtain q where q_def: "q \<in> ?S" "matching_weight q = Min ?W" by auto

    have "\<forall> z \<in> ?S. matching_weight z \<ge> matching_weight q"
      using \<open>finite (matching_weight ` matching_with_edge i j)\<close> q_def(2)
      by force

    then show ?thesis using q_def(1) that by blast
  qed

  have weight_ge: "matching_weight q_best > min_weight_val"
  proof -
    have "p_min \<notin> ?S"
      by (simp add: matching_with_edge_def neq)
    have "is_perfect_matching q_best"
      using matching_with_edge_def q_best_props(1) by auto
    have "matching_weight q_best \<ge> min_weight_val"
      by (simp add: \<open>is_perfect_matching q_best\<close> minimum_weight)
    moreover have "matching_weight q_best \<noteq> min_weight_val"
      using \<open>p_min \<notin> matching_with_edge i j\<close> assms(3)
        matching_with_edge_def q_best_props(1) by blast
    ultimately show ?thesis by simp
  qed

  have div_by_q_best: "(2::int) ^ matching_weight q_best dvd minor_sum i j"
  proof -
    have "\<forall> p \<in> ?S. (2::int) ^ matching_weight q_best dvd (sign p * (\<Prod>k=0..<n. D_entry k (p k)))"
    proof
      fix p assume "p \<in> ?S"
      then have p_pm: "is_perfect_matching p"
        by (simp add: matching_with_edge_def)

      have p_perm: "p permutes {0..<n}"
        using p_pm is_perfect_matching_def by simp

      have w_ge: "matching_weight p \<ge> matching_weight q_best"
        using \<open>p \<in> matching_with_edge i j\<close> q_best_props(2) by blast

      have "abs (sign p * (\<Prod>k=0..<n. D_entry k (p k))) = (2::int) ^ matching_weight p"
        using p_pm p_perm
        by (simp add: abs_mult bipartite_graph.term_value_non_zero) 

      then have "(2::int) ^ matching_weight p dvd (sign p *(\<Prod>k=0..<n. D_entry k (p k)))"
        by (simp add: multiplicity_2_abs multiplicity_dvd')

      then show "(2::int) ^ matching_weight q_best dvd (sign p * (\<Prod>k=0..<n. D_entry k (p k)))"
        using power_le_dvd w_ge by blast
    qed
    then show ?thesis
      by (simp add: dvd_sum minor_sum_def) 
  qed


  have val_ge_best: "multiplicity 2 (minor_sum i j) \<ge> matching_weight q_best"
  proof -
    have "minor_sum i j = D_entry i j * cofactor_sum i j"
      by (simp add: assms(4,5,6) minor_sum_decomposition)
    then have nz: "minor_sum i j \<noteq> 0"
      using cofactor_nz edge_exists unfolding D_entry_def by simp
    show ?thesis
      by (simp add: div_by_q_best multiplicity_geI nz)
  qed

  have val_is_min: "multiplicity 2 (minor_sum i j) = min_weight_val"
  proof -
    have split: "minor_sum i j = D_entry i j * cofactor_sum i j"
      by (simp add: assms(4,5,6) minor_sum_decomposition)

    have D_entry_nz: "D_entry i j \<noteq> 0" unfolding D_entry_def
      using assms(4) by auto

    have "multiplicity 2 (minor_sum i j) = multiplicity 2 (D_entry i j) + multiplicity 2 (cofactor_sum i j)" 
      unfolding split
      using D_entry_nz cofactor_nz 
      by (simp add: prime_elem_multiplicity_mult_distrib)

    also have "... = w i j + multiplicity 2 (cofactor_sum i j)"
      by (simp add: D_entry_def assms(4))

    finally show ?thesis
      by (simp add: assms(7))
  qed

  show False
    using val_ge_best val_is_min weight_ge by linarith
qed


lemma correct_edge_implies_sum_eq:
  fixes p_min :: "nat \<Rightarrow> nat" and i j :: nat
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
  let ?S = "matching_with_edge i j"
  have p_in_S : "p_min \<in> ?S"
    by (simp add: assms(1,7) matching_with_edge_def)

  have unique_in_S: "\<forall>q \<in> ?S - {p_min}. is_perfect_matching q \<longrightarrow> matching_weight q > matching_weight p_min"
    using assms(2,3) minimum_weight by force

  have S_finite: "finite ?S"
    by (simp add: bipartite_graph.finite_perfect_matchings
        matching_with_edge_def)

  have S_permutes: "\<forall>p \<in> ?S. p permutes{0..<n}"
    by (simp add: bipartite_graph.is_perfect_matching_def
        matching_with_edge_def)

  have val_minor: "multiplicity 2 (minor_sum i j) = min_weight_val"
  proof -
    have "minor_sum i j = (\<Sum>p \<in> ?S. sign p * (\<Prod>k = 0..<n. D_entry k (p k)))"
      unfolding minor_sum_def by simp
    also have "multiplicity 2 ... = matching_weight p_min"
      by (rule unique_subset_sum_power_of_weight[OF S_finite p_in_S p_min_def(1) unique_in_S S_permutes])
    finally show ?thesis
      by (simp add: assms(2)) 
  qed

  have split_eq: "minor_sum i j = D_entry i j * cofactor_sum i j"
    by (simp add: assms(4,5,6) minor_sum_decomposition)

  have minor_notzero: "minor_sum i j \<noteq> 0"
  proof -
    have "(\<Sum>p \<in> ?S. sign p * (\<Prod>k=0..<n. D_entry k (p k))) \<noteq> 0"
      using unique_subset_sum_power_of_weight(1)[OF S_finite p_in_S p_min_def(1) unique_in_S S_permutes] 
      by simp

    then show ?thesis
      unfolding minor_sum_def by simp
  qed

  have val_entry: "multiplicity 2 (D_entry i j) = w i j"
    by (simp add: assms(4) bipartite_graph.D_entry_def)

  show ?thesis
    using val_minor split_eq val_entry minor_notzero
    by (simp add: prime_elem_multiplicity_mult_distrib)
qed



theorem edge_test_iff_correct:
  fixes p_min :: "nat \<Rightarrow> nat" and i j :: nat
  assumes p_min_def: "is_perfect_matching p_min" 
          "matching_weight p_min = min_weight_val"
  assumes p_min_unique: "\<forall>q. is_perfect_matching q \<and>
                          matching_weight q = min_weight_val 
                          \<longrightarrow> q = p_min"
  assumes edge_exists: "(i, j) \<in> E"
  assumes i_valid: "i < n" and j_valid: "j < n"
  shows "p_min i = j \<longleftrightarrow> (cofactor_sum i j \<noteq> 0 \<and> w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val)"

proof (rule iffI)
  assume "cofactor_sum i j \<noteq> 0 \<and> w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
  then have nz: "cofactor_sum i j \<noteq> 0" and eq: "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
    by auto
  show "p_min i = j"
    using sum_eq_implies_correct_edge
    using
      \<open>cofactor_sum i j \<noteq> 0 \<and> w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val\<close>
      assms(1,2,3,4,5,6) by blast

next
  assume "p_min i = j"
  have eq: "w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
    using \<open>p_min i = j\<close> assms(2,4,5,6)
      bipartite_graph.correct_edge_implies_sum_eq p_min_def(1)
      p_min_unique by blast
  have nz: "cofactor_sum i j \<noteq> 0"
  proof -
    let ?S = "matching_with_edge i j"

    have p_in_S: "p_min \<in> ?S"
      using \<open>p_min i = j\<close> assms(1) matching_with_edge_def by blast

    have S_finite: "finite ?S"
      by (simp add: bipartite_graph.finite_perfect_matchings
          matching_with_edge_def)

    have unique_in_S: "\<forall> q \<in> ?S - {p_min}. is_perfect_matching q \<longrightarrow> matching_weight q > matching_weight p_min"
      using assms(2,3) minimum_weight by fastforce

    have S_permutes: "\<forall>p \<in> ?S. p permutes{0..<n}"
      by (simp add: is_perfect_matching_def
          matching_with_edge_def)

    have "(\<Sum>p \<in> ?S. sign p * (\<Prod>k=0..<n. D_entry k (p k))) \<noteq> 0"
      using unique_subset_sum_power_of_weight(1)
      using S_finite S_permutes assms(1) p_in_S unique_in_S
      by blast

    then have "minor_sum i j \<noteq> 0" unfolding minor_sum_def .

    then show ?thesis
      by (simp add: assms(4,5,6)
          bipartite_graph.minor_sum_decomposition)
  qed
  show "cofactor_sum i j \<noteq> 0 \<and> w i j + multiplicity 2 (cofactor_sum i j) = min_weight_val"
    using eq nz by simp
qed
end

(* Probability of Case 3 \<le> |E|/N *)

(*
   Isolation Lemma (Set Theory)     Graph Theory Representation
   Universe (U)                     The set of all edges E
   Element (x \<in> U)                  A single edge (i, j)
   Weight function (w)              The edge weight matrix w
   Feasible Solution (S)            A perfect matching p (as a set of edges)
   Family of Solutions (F)          The collection of all valid perfect matchings(set of sets)
*)

definition matching_to_set :: 
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<times> nat) set" where 
    "matching_to_set n p = {(i, p i)| i. i < n}"

definition perfect_matching_family :: 
    "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> ((nat \<times> nat) set) set" where
    "perfect_matching_family n E = 
      {matching_to_set n p | p. p permutes{0..<n} \<and> (\<forall>i < n. (i, p i) \<in> E)}"

context bipartite_graph
begin

lemma matching_to_set_inj:
  assumes "p permutes {0..<n}" "q permutes {0..<n}"
  assumes "matching_to_set n p = matching_to_set n q"
  shows "p = q"
proof -
  have "\<forall> i < n. p i = q i"
  proof (intro allI impI)
    fix i assume "i < n"
    have "(i, p i) \<in> matching_to_set n p"
      using `i < n` matching_to_set_def by auto

    then have "(i,p i) \<in> matching_to_set n q"
      using assms(3) by simp

    then show "p i = q i"
      using matching_to_set_def `i < n` by auto

  qed
  then show "p = q"
    by (metis (no_types, lifting) ext assms(1,2) atLeastLessThan_iff
        permutes_not_in)
qed

lemma weight_equivalence:
  assumes "p permutes {0..<n}"
  shows "wt w_func (matching_to_set n p) = bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p"
proof -
  have inj_proof: "inj_on (\<lambda>i. (i, p i)) {0..<n}"
    by (auto simp: inj_on_def)

  have set_is_image: "matching_to_set n p = (\<lambda>i. (i, p i)) ` {0..<n}"
    unfolding matching_to_set_def image_def by auto

  have "wt w_func (matching_to_set n p) = (\<Sum>e \<in> (matching_to_set n p). w_func e)"
    unfolding wt_def ..
    
  also have "... = (\<Sum>i \<in> {0..<n}. w_func (i, p i))"
    unfolding matching_to_set_def
    using sum.reindex[OF inj_proof]
    using matching_to_set_def set_is_image by auto 

  also have "... = bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p"
    unfolding bipartite_graph.matching_weight_def by simp

  finally show ?thesis by simp
qed


lemma pm_iso_equivalence:
  fixes w_func :: "nat \<times> nat \<Rightarrow> nat"
  
  shows "bipartite_graph.unique_min_weight_condition n (\<lambda>u v. w_func(u,v)) E \<longleftrightarrow> has_unique_minimizer (perfect_matching_family n E) w_func"

proof -
  let ?Graph_Cond = "bipartite_graph.unique_min_weight_condition n (\<lambda>u v. w_func(u,v)) E"
  let ?F = "perfect_matching_family n E"
  let ?Set_Cond = "has_unique_minimizer (perfect_matching_family n E) w_func"

  show "?Graph_Cond \<longleftrightarrow> ?Set_Cond"
  proof 
    assume ?Graph_Cond

    obtain p where p_unique:
      "bipartite_graph.is_perfect_matching n E p"
      "bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p = bipartite_graph.min_weight_val n (\<lambda>u v. w_func(u,v)) E"
      "\<forall>q. bipartite_graph.is_perfect_matching n E q \<and> 
           bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) q = bipartite_graph.min_weight_val n (\<lambda>u v. w_func(u,v)) E \<longrightarrow> q = p"
      using `?Graph_Cond` unfolding bipartite_graph.unique_min_weight_condition_def
      by auto

    let ?S_p = "matching_to_set n p"

    have is_min: "minimizer ?F w_func ?S_p"
      unfolding minimizer_def perfect_matching_family_def
    proof (intro conjI)
      show "?S_p \<in> {matching_to_set n p |p. p permutes {0..<n} \<and> (\<forall>i<n. (i, p i) \<in> E)}"
        using p_unique(1) bipartite_graph.is_perfect_matching_def by auto

    next
      show "\<forall>S \<in> {matching_to_set n p |p. p permutes {0..<n} \<and> (\<forall>i<n. (i, p i) \<in> E)}.
            wt w_func ?S_p \<le> wt w_func S"
      proof (intro ballI)
        fix S assume "S \<in> {matching_to_set n p |p. p permutes {0..<n} \<and> (\<forall>i<n. (i, p i) \<in> E)}"
        then obtain q where q_def: "S = matching_to_set n q" "bipartite_graph.is_perfect_matching n E q"
          unfolding bipartite_graph.is_perfect_matching_def by auto

        have "wt w_func ?S_p = bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p"
          using bipartite_graph.is_perfect_matching_def p_unique(1)
            weight_equivalence by presburger
        also have "... \<le> bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) q"
          by (simp add: bipartite_graph.minimum_weight p_unique(2)
              q_def(2))
        also have "... = wt w_func S"
          using is_perfect_matching_def q_def(1,2) weight_equivalence
          by auto
        finally show "wt w_func ?S_p \<le> wt w_func S" .
        qed
      qed
      have "\<forall>S \<in> ?F. minimizer ?F w_func S \<longrightarrow> S = ?S_p"
      proof (intro ballI impI)
        fix S assume "S \<in> ?F" "minimizer ?F w_func S"
        then obtain q where q_def: "S = matching_to_set n q" "bipartite_graph.is_perfect_matching n E q"
          unfolding perfect_matching_family_def bipartite_graph.is_perfect_matching_def by auto

        have "wt w_func S = wt w_func ?S_p"
          using is_min
          using \<open>minimizer (perfect_matching_family n E) w_func S\<close>
            minimizers_same_weight by blast 

        then have "bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) q = bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p"
          by (metis is_perfect_matching_def p_unique(1) q_def(1,2)
              weight_equivalence)

        then have "p = q"
          using p_unique(2,3) q_def(2) by auto

        then show "S = ?S_p" using q_def(1) by simp
      qed
    show ?Set_Cond
      unfolding has_unique_minimizer_def
      using
        \<open>\<forall>S\<in>perfect_matching_family n E. minimizer (perfect_matching_family n E) w_func S \<longrightarrow> S = matching_to_set n p\<close>
        is_min minimizer_def by blast 
  next
    assume ?Set_Cond

    obtain S where S_unique: "minimizer ?F w_func S" "\<forall>S' \<in> ?F. minimizer ?F w_func S' \<longrightarrow> S' = S"
      using `?Set_Cond` has_unique_minimizer_def
      by metis

    obtain p where p_def: "S = matching_to_set n p" "bipartite_graph.is_perfect_matching n E p"
      using S_unique(1) minimizer_def perfect_matching_family_def bipartite_graph.is_perfect_matching_def
      by (smt (verit, del_insts) mem_Collect_eq)

    show ?Graph_Cond
      unfolding bipartite_graph.unique_min_weight_condition_def
    proof (intro ex1I conjI)
      show "bipartite_graph.is_perfect_matching n E p" using p_def(2) .

      show "bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p = bipartite_graph.min_weight_val n (\<lambda>u v. w_func(u,v)) E"
      proof -
        let ?Weights = "{bipartite_graph.matching_weight n (\<lambda>u v. w_func (u, v)) q |q. bipartite_graph.is_perfect_matching n E q}"

        have "finite ?Weights"
          using bipartite_graph.finite_perfect_matchings by auto

        have p_in_weights: "bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p \<in> ?Weights"
          using p_def(2) by auto

        have p_min: "\<forall>y \<in> ?Weights. bipartite_graph.matching_weight n (\<lambda>u v. w_func(u, v)) p \<le> y"
        proof
          fix y assume "y \<in> ?Weights"
          then obtain q where q_info: "y = bipartite_graph.matching_weight n (\<lambda>u v. w_func(u, v)) q" " bipartite_graph.is_perfect_matching n E q"
            by auto

          let ?S_q = "matching_to_set n q"

          have Sq_in_family: "?S_q \<in> perfect_matching_family n E"
            using bipartite_graph.is_perfect_matching_def
              perfect_matching_family_def q_info(2) by auto

          have "wt w_func S \<le> wt w_func ?S_q"
            using S_unique(1) Sq_in_family minimizer_def by auto
        
          then show "bipartite_graph.matching_weight n (\<lambda>u v. w_func (u,v)) p \<le> y"
            by (metis bipartite_graph.is_perfect_matching_def
                bipartite_graph.weight_equivalence p_def(1,2) q_info(1,2))
        qed
        have "bipartite_graph.matching_weight n (\<lambda>u v. w_func (u,v)) p = Min ?Weights"
          by (metis (no_types, lifting) Min_eqI
              \<open>finite {bipartite_graph.matching_weight n (\<lambda>u v. w_func (u, v)) q |q. is_perfect_matching q}\<close>
              p_in_weights p_min)
        then show ?thesis
            using
              \<open>bipartite_graph.matching_weight n (\<lambda>u v. w_func (u, v)) p = Min {bipartite_graph.matching_weight n (\<lambda>u v. w_func (u, v)) q |q. is_perfect_matching q}\<close>
              bipartite_graph.min_weight_val_def by auto 
        qed

        fix q assume q_asm: "bipartite_graph.is_perfect_matching n E q \<and> 
                           bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) q = bipartite_graph.min_weight_val n (\<lambda>u v. w_func(u,v)) E"

        let ?S_q = "matching_to_set n q"

        have "wt w_func ?S_q = wt w_func S"
        proof -
          have Sq_eq_q: "wt w_func ?S_q = bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) q"
            using bipartite_graph.is_perfect_matching_def q_asm
              weight_equivalence by blast
          also have "... = bipartite_graph.matching_weight n (\<lambda>u v. w_func(u,v)) p"
            using
              \<open>bipartite_graph.matching_weight n (\<lambda>u v. w_func (u, v)) p = bipartite_graph.min_weight_val n (\<lambda>u v. w_func (u, v)) E\<close>
              q_asm by force
          also have "... = wt w_func S"
            by (metis is_perfect_matching_def p_def(1,2)
                weight_equivalence)
          finally show ?thesis .
        qed

        have "?S_q = S"
        proof -
          have Sq_in_F: "?S_q \<in> ?F"
            using q_asm unfolding perfect_matching_family_def bipartite_graph.is_perfect_matching_def by auto

          have "minimizer ?F w_func ?S_q"
            by (metis S_unique(1) Sq_in_F
                \<open>wt w_func (matching_to_set n q) = wt w_func S\<close>
                minimizer_def)

          show ?thesis
            by (simp add: S_unique(2) Sq_in_F
                \<open>minimizer (perfect_matching_family n E) w_func (matching_to_set n q)\<close>)
        qed

        show "q = p"
          using \<open>matching_to_set n q = S\<close> is_perfect_matching_def
            matching_to_set_inj p_def(1,2) q_asm by presburger
      qed
    qed
qed



lemma isolation_lemma_for_perfect_matching:
  fixes N :: nat
  assumes "N \<ge> 1"
  assumes "\<exists>p. is_perfect_matching p"
  assumes "E \<subseteq> {0..<n} \<times> {0..<n}"

shows "measure_pmf.prob (w_pmf N E)
      {w. bipartite_graph.unique_min_weight_condition n (\<lambda>u v. w(u,v)) E}
      \<ge> 1 - (real (card E)/ real N)"
proof -
  let ?U = E
  let ?F = "perfect_matching_family n E"

  have condition_eq: 
    "{w. bipartite_graph.unique_min_weight_condition n (\<lambda>u v. w(u,v)) E} = {w. has_unique_minimizer ?F w}"
    by (simp add: pm_iso_equivalence)

  have "finite ?U"
  proof -
    have "finite ({0..<n} \<times> {0..<n})" by simp
    then show "finite E"
      using assms(3) finite_subset by blast
  qed

  have "?F \<subseteq> Pow ?U"
    unfolding perfect_matching_family_def matching_to_set_def bipartite_graph.is_perfect_matching_def
    by blast

  have "?F \<noteq> {}"
  proof -
    obtain p where "bipartite_graph.is_perfect_matching n E p"
      using assms(2) by auto
    then have "matching_to_set n p \<in> ?F"
      unfolding perfect_matching_family_def
      using is_perfect_matching_def by auto
    then show ?thesis by auto
  qed

  have prob_bound: "measure_pmf.prob (w_pmf N ?U){w. has_unique_minimizer ?F w} \<ge> 1 - real(card ?U)/real N"
    using isolation_lemma_main[of ?U ?F N]
    using `finite ?U` `?F \<subseteq> Pow ?U` `?F \<noteq> {}` `N \<ge> 1` 
    by simp

  show ?thesis
    by (simp add: condition_eq prob_bound)
qed
end
end
